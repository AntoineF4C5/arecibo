//! This module defines the Nova augmented circuit used for Cyclefold

use crate::{
  constants::{BN_N_LIMBS, NIO_CYCLE_FOLD, NUM_FE_IN_EMULATED_POINT, NUM_HASH_BITS},
  gadgets::{
    alloc_num_equals, alloc_scalar_as_base, alloc_zero, le_bits_to_num,
    AllocatedRelaxedR1CSInstance,
  },
  traits::{
    commitment::CommitmentTrait, CurveCycleEquipped, Dual, Engine, ROCircuitTrait,
    ROConstantsCircuit,
  },
  Commitment,
};

use abomonation_derive::Abomonation;
use bellpepper::gadgets::{
  boolean::Boolean,
  boolean_utils::{conditionally_select, conditionally_select_slice},
  num::AllocatedNum,
  Assignment,
};
use bellpepper_core::{boolean::AllocatedBit, ConstraintSystem, SynthesisError};
use ff::Field;
use serde::{Deserialize, Serialize};

use crate::cyclefold::{
  gadgets::{emulated, AllocatedCycleFoldData},
  util::FoldingData,
};

use super::rs::StepCircuit;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize, Abomonation)]
struct AugmentedCircuitParams {
  limb_width: usize,
  n_limbs: usize,
}

impl AugmentedCircuitParams {
  pub const fn new(limb_width: usize, n_limbs: usize) -> Self {
    Self {
      limb_width,
      n_limbs,
    }
  }
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(bound = "")]
struct AugmentedCircuitInputs<E1>
where
  E1: CurveCycleEquipped,
{
  pp_digest: E1::Base,
  i: E1::Scalar,
  z0: Vec<E1::Scalar>,

  zi: Option<Vec<E1::Scalar>>,
  data_p: Option<FoldingData<E1>>,

  data_c_1: Option<FoldingData<Dual<E1>>>,
  data_c_2: Option<FoldingData<Dual<E1>>>,

  E_new: Option<Commitment<E1>>,
  W_new: Option<Commitment<E1>>,

  prev_IC: Option<E1::Base>,
  comm_omega_prev: Option<Commitment<E1>>,
}
