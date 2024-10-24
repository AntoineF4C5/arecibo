use std::marker::PhantomData;

use crate::constants::NUM_HASH_BITS;
use crate::gadgets::scalar_as_base;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::AbsorbInROTrait;
use crate::traits::CurveCycleEquipped;
use crate::traits::Dual;
use crate::traits::ROTrait;
use crate::{
  traits::{Engine, ROConstants},
  CommitmentKey,
};
use ff::Field;

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
  pub fn commit(
    ck: &CommitmentKey<E1>,
    ro_consts: &ROConstants<Dual<E1>>,
    prev_comm: E1::Base,
    w_input: Vec<E1::Scalar>, // non-deterministic witness ω
  ) -> E1::Base {
    let comm_w_input = E1::CE::commit(ck, &w_input);
    let mut ro = <Dual<E1> as Engine>::RO::new(ro_consts.clone(), 4); // prev_comm, x, y, inf

    // ro.absorb(scalar_as_base::<E1>(prev_comm));
    // comm_w_input.absorb_in_ro(&mut ro);
    ro.squeeze(NUM_HASH_BITS)
  }
}
