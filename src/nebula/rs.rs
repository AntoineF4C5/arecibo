use crate::cyclefold::nifs::PrimaryNIFS;
use crate::traits::commitment::CommitmentEngineTrait;

use crate::Commitment;
use crate::{
  bellpepper::{
    r1cs::{NovaShape, NovaWitness},
    shape_cs::ShapeCS,
    solver::SatisfyingAssignment,
  },
  constants::{
    BN_LIMB_WIDTH, BN_N_LIMBS, NIO_CYCLE_FOLD, NUM_CHALLENGE_BITS, NUM_FE_IN_EMULATED_POINT,
    NUM_HASH_BITS,
  },
  cyclefold::circuit::CycleFoldCircuit,
  errors::NovaError,
  gadgets::scalar_as_base,
  r1cs::{
    self, CommitmentKeyHint, R1CSInstance, R1CSResult, R1CSWitness, RelaxedR1CSInstance,
    RelaxedR1CSWitness,
  },
  traits::{
    commitment::CommitmentTrait, AbsorbInROTrait, CurveCycleEquipped, Dual, Engine,
    ROConstantsCircuit, ROTrait,
  },
  CommitmentKey, DigestComputer, R1CSWithArity, ROConstants, ResourceBuffer, SimpleDigestible,
};
use bellpepper_core::num::AllocatedNum;
use ff::Field;
use serde::{Deserialize, Serialize};

use abomonation::Abomonation;
use abomonation_derive::Abomonation;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use ff::{PrimeField, PrimeFieldBits};
use once_cell::sync::OnceCell;

use super::augmented_circuit::{AugmentedCircuit, AugmentedCircuitParams};

/// The public parameters used in the CycleFold recursive SNARK proof and verification
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize, Abomonation)]
#[serde(bound = "")]
#[abomonation_bounds(
where
  E1: CurveCycleEquipped,
  <E1::Scalar as PrimeField>::Repr: Abomonation,
  <<Dual<E1> as Engine>::Scalar as PrimeField>::Repr: Abomonation,
)]
pub struct PublicParams<E1>
where
  E1: CurveCycleEquipped,
{
  F_arity_primary: usize,
  ro_consts_primary: ROConstants<Dual<E1>>,
  ro_consts_circuit_primary: ROConstantsCircuit<Dual<E1>>,
  ck_primary: CommitmentKey<E1>,
  circuit_shape_primary: R1CSWithArity<E1>,
  augmented_circuit_params: AugmentedCircuitParams,
  ro_consts_cyclefold: ROConstants<Dual<E1>>,
  ro_consts_secondary: ROConstants<E1>,
  ck_cyclefold: CommitmentKey<Dual<E1>>,
  circuit_shape_cyclefold: R1CSWithArity<Dual<E1>>,
  #[abomonation_skip]
  #[serde(skip, default = "OnceCell::new")]
  digest: OnceCell<E1::Scalar>,
}

impl<E1> PublicParams<E1>
where
  E1: CurveCycleEquipped,
{
  /// Builds the public parameters for the circuit `C1`.
  /// The same note for public parameter hints apply as in the case for Nova's public parameters:
  /// For some final compressing SNARKs the size of the commitment key must be larger, so we include
  /// `ck_hint_primary` and `ck_hint_cyclefold` parameters to accommodate this.
  pub fn setup<C1: StepCircuit<E1::Scalar>>(
    c_primary: &C1,
    ck_hint_primary: &CommitmentKeyHint<E1>,
    ck_hint_cyclefold: &CommitmentKeyHint<Dual<E1>>,
  ) -> Self {
    let F_arity_primary = c_primary.arity();
    let ro_consts_primary = ROConstants::<Dual<E1>>::default();
    let ro_consts_circuit_primary = ROConstantsCircuit::<Dual<E1>>::default();

    let augmented_circuit_params = AugmentedCircuitParams::new(BN_LIMB_WIDTH, BN_N_LIMBS);
    let circuit_primary: AugmentedCircuit<'_, Dual<E1>, E1, C1> = AugmentedCircuit::new(
      &augmented_circuit_params,
      ro_consts_circuit_primary.clone(),
      None,
      c_primary,
    );
    let mut cs: ShapeCS<E1> = ShapeCS::new();
    let _ = circuit_primary.synthesize(&mut cs);
    let (r1cs_shape_primary, ck_primary) = cs.r1cs_shape_and_key(ck_hint_primary);
    let circuit_shape_primary = R1CSWithArity::new(r1cs_shape_primary, F_arity_primary);

    let ro_consts_cyclefold = ROConstants::<Dual<E1>>::default();
    let mut cs: ShapeCS<Dual<E1>> = ShapeCS::new();
    let circuit_cyclefold: CycleFoldCircuit<E1> = CycleFoldCircuit::default();
    let _ = circuit_cyclefold.synthesize(&mut cs);
    let (r1cs_shape_cyclefold, ck_cyclefold) = cs.r1cs_shape_and_key(ck_hint_cyclefold);
    let circuit_shape_cyclefold = R1CSWithArity::new(r1cs_shape_cyclefold, 0);

    Self {
      F_arity_primary,
      ro_consts_primary,
      ro_consts_circuit_primary,
      ck_primary,
      circuit_shape_primary,
      augmented_circuit_params,
      ro_consts_cyclefold,
      ck_cyclefold,
      circuit_shape_cyclefold,
      digest: OnceCell::new(),
      ro_consts_secondary: ROConstants::<E1>::default(),
    }
  }

  /// Calculate the digest of the public parameters.
  pub fn digest(&self) -> E1::Scalar {
    self
      .digest
      .get_or_try_init(|| DigestComputer::new(self).digest())
      .cloned()
      .expect("Failure in retrieving digest")
  }

  /// Returns the number of constraints in the primary and cyclefold circuits
  pub const fn num_constraints(&self) -> (usize, usize) {
    (
      self.circuit_shape_primary.r1cs_shape.num_cons,
      self.circuit_shape_cyclefold.r1cs_shape.num_cons,
    )
  }

  /// Returns the number of variables in the primary and cyclefold circuits
  pub const fn num_variables(&self) -> (usize, usize) {
    (
      self.circuit_shape_primary.r1cs_shape.num_vars,
      self.circuit_shape_cyclefold.r1cs_shape.num_vars,
    )
  }
}

impl<E1> SimpleDigestible for PublicParams<E1> where E1: CurveCycleEquipped {}

/// A SNARK that proves the correct execution of an incremental computation in the CycleFold folding
/// scheme.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct RecursiveSNARK<E1>
where
  E1: CurveCycleEquipped,
{
  // primary circuit data
  r_W_primary: RelaxedR1CSWitness<E1>,
  r_U_primary: RelaxedR1CSInstance<E1>,
  l_w_primary: R1CSWitness<E1>,
  l_u_primary: R1CSInstance<E1>,

  i: usize,

  // incremental commitment of previous invokation of step circuit
  IC_i_minus_one: E1::Scalar,

  // commitment to non-deterministic advice
  IC_W: Commitment<E1>, // supposed to be contained in self.l_u_primary // corresponds to comm_W in self.l_u_primary
}

impl<E1> RecursiveSNARK<E1>
where
  E1: CurveCycleEquipped,
{
  pub fn new<C>(pp: &PublicParams<E1>, c: &C) -> Result<Self, NovaError>
  where
    C: StepCircuit<E1::Scalar>,
  {
    let r1cs_primary = &pp.circuit_shape_primary.r1cs_shape;

    let r_U_primary = RelaxedR1CSInstance::default(&pp.ck_primary, r1cs_primary);
    let r_W_primary = RelaxedR1CSWitness::default(r1cs_primary);

    let mut cs_primary = SatisfyingAssignment::<E1>::new();
    let (l_u_primary, l_w_primary) =
      cs_primary.r1cs_instance_and_witness(r1cs_primary, &pp.ck_primary)?;

    Ok(Self {
      // IVC proof
      r_W_primary,
      r_U_primary,
      l_w_primary,
      l_u_primary,

      i: 0,

      // incremental commitment
      IC_i_minus_one: E1::Scalar::ZERO, // IC_0 = ⊥, // carries value of: C_i−1

      // commitment to non-deterministic advice
      IC_W: c.commit_w::<E1>(&pp.ck_primary), // C_ω_i−1
    })
  }

  pub fn prove_step<C>(
    &mut self,
    pp: &PublicParams<E1>,
    c: &C,
    IC_i: E1::Scalar,
  ) -> Result<E1::Scalar, NovaError>
  // outputs IC_i
  where
    C: StepCircuit<E1::Scalar>,
  {
    if self.i == 0 {
      self.i = 1;
      return Ok(IC_i);
    }
    // Parse Πi (self) as ((Ui, Wi), (ui, wi)) and then:
    //
    // 1. compute (Ui+1,Wi+1,T) ← NIFS.P(pk,(Ui,Wi),(ui,wi)),
    let (nifs_primary, (r_U_primary, r_W_primary), r) = PrimaryNIFS::<E1, Dual<E1>>::prove(
      &pp.ck_primary,
      &pp.ro_consts_primary,
      &pp.digest(),
      &pp.circuit_shape_primary.r1cs_shape,
      &self.r_U_primary,
      &self.r_W_primary,
      &self.l_u_primary,
      &self.l_w_primary,
    )?;
    let comm_T = Commitment::<E1>::decompress(&nifs_primary.comm_T)?;

    // Abort if Ci  != hash(Ci−1, Cωi−1 )
    let intermediary_comm = {
      let mut ro = E1::RO::new(pp.ro_consts_secondary.clone(), 4); // prev_comm, x, y, inf

      ro.absorb(scalar_as_base::<E1>(self.IC_i_minus_one));
      self.IC_W.absorb_in_ro(&mut ro);
      ro.squeeze(NUM_HASH_BITS)
    };

    if IC_i != intermediary_comm {
      return Err(NovaError::InvalidIC);
    }

    // 2. compute (ui+1, wi+1) ← trace(F ′, (vk, Ui, ui, (i, z0, zi), ωi, T )),
    let mut cs_primary = SatisfyingAssignment::<E1>::with_capacity(
      pp.circuit_shape_primary.r1cs_shape.num_io + 1,
      pp.circuit_shape_primary.r1cs_shape.num_vars,
    );
    let (l_u_primary, l_w_primary) = cs_primary
      .r1cs_instance_and_witness(&pp.circuit_shape_primary.r1cs_shape, &pp.ck_primary)
      .map_err(|_| NovaError::UnSat)?;

    // 3. output Πi+1 ← ((Ui+1, Wi+1), (ui+1, wi+1)).
    self.r_U_primary = r_U_primary;
    self.r_W_primary = r_W_primary;
    self.l_u_primary = l_u_primary;
    self.l_w_primary = l_w_primary;

    // update incremental commitments in IVC proof
    self.IC_i_minus_one = IC_i;
    self.IC_W = c.commit_w::<E1>(&pp.ck_primary);

    self.i += 1;

    Ok(IC_i)
  }
}

/// A helper trait for a step of the incremental computation (i.e., circuit for F)
pub trait StepCircuit<F: PrimeField>: Send + Sync + Clone {
  /// Return the number of inputs or outputs of each step
  /// (this method is called only at circuit synthesis time)
  /// `synthesize` and `output` methods are expected to take as
  /// input a vector of size equal to arity and output a vector of size equal to arity
  fn arity(&self) -> usize;

  /// Sythesize the circuit for a computation step and return variable
  /// that corresponds to the output of the step `z_{i+1}`
  fn synthesize<CS: ConstraintSystem<F>>(
    &self,
    cs: &mut CS,
    z: &[AllocatedNum<F>],
  ) -> Result<Vec<AllocatedNum<F>>, SynthesisError>;

  // Get the non-deterministic advice we will commit to
  fn non_deterministic_advice(&self) -> Vec<F>;

  fn commit_w<E>(&self, ck: &CommitmentKey<E>) -> Commitment<E>
  where
    E: Engine<Scalar = F>,
  {
    E::CE::commit(ck, &self.non_deterministic_advice())
  }
}

#[cfg(test)]
mod test {
  use std::marker::PhantomData;

  use bellpepper_core::num::AllocatedNum;

  use super::*;
  use crate::{
    nebula::ic::IC,
    provider::{Bn256EngineKZG, PallasEngine, Secp256k1Engine},
    traits::snark::default_ck_hint,
  };

  #[derive(Clone)]
  struct SquareCircuit<F> {
    _p: PhantomData<F>,
  }

  impl<F: PrimeField> StepCircuit<F> for SquareCircuit<F> {
    fn arity(&self) -> usize {
      1
    }

    fn synthesize<CS: ConstraintSystem<F>>(
      &self,
      cs: &mut CS,
      z: &[AllocatedNum<F>],
    ) -> Result<Vec<AllocatedNum<F>>, SynthesisError> {
      let x = &z[0];
      let x_sq = x.square(cs.namespace(|| "x_sq"))?;

      Ok(vec![x_sq])
    }

    fn non_deterministic_advice(&self) -> Vec<F> {
      vec![F::ZERO; 3]
    }
  }

  fn test_trivial_cyclefold_prove_verify_with<E: CurveCycleEquipped>() {
    let primary_circuit = SquareCircuit::<E::Scalar> { _p: PhantomData };

    let pp = PublicParams::<E>::setup(&primary_circuit, &*default_ck_hint(), &*default_ck_hint());

    let z0 = vec![E::Scalar::from(2u64)];

    let mut recursive_snark = RecursiveSNARK::new(&pp, &primary_circuit).unwrap();
    let mut IC_i = E::Scalar::ZERO;

    (0..5).for_each(|iter| {
      let incremental_commitment = recursive_snark
        .prove_step(&pp, &primary_circuit, IC_i)
        .unwrap();

      IC_i = IC::<E>::commit(
        &pp.ck_primary,
        &pp.ro_consts_secondary,
        incremental_commitment,
        primary_circuit.non_deterministic_advice(),
      );
    });
  }

  #[test]
  fn test_cyclefold_prove_verify() {
    test_trivial_cyclefold_prove_verify_with::<PallasEngine>();
    test_trivial_cyclefold_prove_verify_with::<Bn256EngineKZG>();
    test_trivial_cyclefold_prove_verify_with::<Secp256k1Engine>();
  }
}
