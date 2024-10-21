use std::marker::PhantomData;

use crate::constants::NUM_HASH_BITS;
use crate::gadgets::scalar_as_base;
use crate::traits::commitment::CommitmentEngineTrait;
use crate::traits::AbsorbInROTrait;
use crate::traits::ROTrait;
use crate::{
  traits::{Engine, ROConstants},
  CommitmentKey,
};

pub struct IC<E1>
where
  E1: Engine,
{
  _p: PhantomData<E1>,
}

impl<E1> IC<E1>
where
  E1: Engine,
{
  pub fn commit(
    ck: &CommitmentKey<E1>,
    ro_consts: &ROConstants<E1>,
    prev_comm: E1::Scalar,
    w_input: Vec<E1::Scalar>,
  ) -> E1::Scalar {
    let comm_w_input = E1::CE::commit(ck, &w_input);
    let mut ro = E1::RO::new(ro_consts.clone(), 4); // prev_comm, x, y, inf

    ro.absorb(scalar_as_base::<E1>(prev_comm));
    comm_w_input.absorb_in_ro(&mut ro);
    ro.squeeze(NUM_HASH_BITS)
  }
}
