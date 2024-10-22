use serde::{Deserialize, Serialize};

use crate::cyclefold::nifs::PrimaryNIFS;
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
    circuit::StepCircuit, commitment::CommitmentTrait, AbsorbInROTrait, CurveCycleEquipped, Dual,
    Engine, ROConstantsCircuit, ROTrait,
  },
  Commitment, CommitmentKey, DigestComputer, R1CSWithArity, ROConstants, ResourceBuffer,
  SimpleDigestible,
};

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
}

impl<E1> RecursiveSNARK<E1>
where
  E1: CurveCycleEquipped,
{
  pub fn prove_step(&self, pp: &PublicParams<E1>) -> Result<(), NovaError> {
    // compute (Ui+1,Wi+1,T) ← NIFS.P(pk,(Ui,Wi),(ui,wi)),
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

    Ok(())
  }
}
