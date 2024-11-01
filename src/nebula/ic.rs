use std::marker::PhantomData;

use crate::constants::NUM_FE_IN_EMULATED_POINT;
use crate::constants::NUM_HASH_BITS;
use crate::cyclefold::util::absorb_primary_commitment;
use crate::gadgets::scalar_as_base;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::CurveCycleEquipped;
use crate::traits::Dual;
use crate::traits::ROTrait;
use crate::Commitment;
use crate::{
  traits::{Engine, ROConstants},
  CommitmentKey,
};

pub struct IC<E1>
where
  E1: CurveCycleEquipped,
{
  _p: PhantomData<E1>,
}

impl<E1> IC<E1>
where
  E1: CurveCycleEquipped,
{
  /// Produce an incremental commitment to a non-deterministic advice ω
  ///
  /// * commits to advice with Pedersen
  /// * hashes previous commitment & pedersen commitment to advice
  /// * outputs hash bits as scalar
  pub fn commit(
    ck: &CommitmentKey<E1>,
    ro_consts: &ROConstants<Dual<E1>>,
    prev_comm: E1::Scalar,
    w_input: Vec<E1::Scalar>, // non-deterministic witness ω
  ) -> E1::Scalar {
    let comm_w_input = E1::CE::commit(ck, &w_input);
    let mut ro = <Dual<E1> as Engine>::RO::new(ro_consts.clone(), 1 + NUM_FE_IN_EMULATED_POINT); // prev_comm + comm_omega

    ro.absorb(prev_comm);
    absorb_primary_commitment::<E1, Dual<E1>>(&comm_w_input, &mut ro);
    scalar_as_base::<Dual<E1>>(ro.squeeze(NUM_HASH_BITS))
  }

  /// Produce an incremental commitment to already pedersen committed non-deterministic advice ω
  pub fn increment_comm_w(
    ro_consts: &ROConstants<Dual<E1>>,
    prev_comm: E1::Scalar,
    comm_w_input: Commitment<E1>, // commitment to non-deterministic witness ω
  ) -> E1::Scalar {
    let mut ro = <Dual<E1> as Engine>::RO::new(ro_consts.clone(), 1 + NUM_FE_IN_EMULATED_POINT); // prev_comm + comm_omega

    ro.absorb(prev_comm);
    absorb_primary_commitment::<E1, Dual<E1>>(&comm_w_input, &mut ro);
    scalar_as_base::<Dual<E1>>(ro.squeeze(NUM_HASH_BITS))
  }
}
