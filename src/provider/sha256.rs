//! SHA-256-based random oracles for Nova's native and circuit models.

use crate::{
  frontend::{
    gadgets::sha256::sha256, num::AllocatedNum, AllocatedBit, Boolean, ConstraintSystem,
    SynthesisError,
  },
  gadgets::utils::le_bits_to_num,
  traits::{ROCircuitTrait, ROTrait},
};
use ff::{PrimeField, PrimeFieldBits};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const ENCODED_FIELD_BITS: usize = 256;
const MAX_CHALLENGE_BITS: usize = 255;
const DEFAULT_DOMAIN: [u8; 8] = *b"NOVA_RO1";
const FIELD_SEQUENCE_TAG: u8 = 1;

/// Parameters for the SHA-256 random oracle.
///
/// The domain is serialized as part of Nova's public parameters. Its default
/// value identifies the framing and digest-to-field rules implemented here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Sha256ROConstants {
  domain: [u8; 8],
}

impl Default for Sha256ROConstants {
  fn default() -> Self {
    Self {
      domain: DEFAULT_DOMAIN,
    }
  }
}

/// A SHA-256 random oracle for native computations.
///
/// Absorbed elements are encoded as:
///
/// ```text
/// domain[8] || type=FIELD_SEQUENCE[1] || element_width_u16_be[2]
///   || element_count_u64_be[8] || field_element_0_be[32] || ...
/// ```
///
/// Each field element uses its unique integer representative, zero-padded to
/// 32 bytes. The element count makes the fixed-width sequence self-framing.
#[derive(Serialize, Deserialize)]
pub struct Sha256RO<Base: PrimeField> {
  state: Vec<Base>,
  constants: Sha256ROConstants,
}

fn field_to_bytes<Base: PrimeFieldBits>(element: &Base) -> [u8; 32] {
  assert!(Base::NUM_BITS as usize <= ENCODED_FIELD_BITS);

  let bits = element.to_le_bits();
  assert!(bits.len() <= ENCODED_FIELD_BITS);

  let mut bytes = [0u8; ENCODED_FIELD_BITS / 8];
  for (bit_index, bit) in bits.iter().enumerate() {
    if *bit {
      let byte_index = bytes.len() - 1 - bit_index / 8;
      bytes[byte_index] |= 1 << (bit_index % 8);
    }
  }
  bytes
}

fn digest_to_field<Base: PrimeField>(
  digest: &[u8; 32],
  num_bits: usize,
  start_with_one: bool,
) -> Base {
  assert!(num_bits <= MAX_CHALLENGE_BITS);
  assert!(num_bits < Base::NUM_BITS as usize);
  assert!(num_bits > 0 || !start_with_one);

  let mut result = Base::ZERO;
  let mut coefficient = Base::ONE;
  for bit_index in 0..num_bits {
    let digest_bit = (digest[31 - bit_index / 8] >> (bit_index % 8)) & 1 == 1;
    if digest_bit || (start_with_one && bit_index == num_bits - 1) {
      result += coefficient;
    }
    coefficient = coefficient.double();
  }
  result
}

fn challenge_capacity<Base: PrimeField>() -> usize {
  MAX_CHALLENGE_BITS.min(Base::NUM_BITS as usize - 1)
}

impl<Base: PrimeFieldBits> Sha256RO<Base> {
  fn digest(&self) -> [u8; 32] {
    let element_count = u64::try_from(self.state.len()).expect("RO state length fits in u64");
    let mut hasher = Sha256::new();
    hasher.update(self.constants.domain);
    hasher.update([FIELD_SEQUENCE_TAG]);
    hasher.update((ENCODED_FIELD_BITS as u16 / 8).to_be_bytes());
    hasher.update(element_count.to_be_bytes());
    for element in &self.state {
      hasher.update(field_to_bytes(element));
    }
    hasher.finalize().into()
  }
}

impl<Base> ROTrait<Base> for Sha256RO<Base>
where
  Base: PrimeFieldBits + Serialize + for<'de> Deserialize<'de>,
{
  type CircuitRO = Sha256ROCircuit<Base>;
  type Constants = Sha256ROConstants;

  fn new(constants: Self::Constants) -> Self {
    Self {
      state: Vec::new(),
      constants,
    }
  }

  fn absorb(&mut self, element: Base) {
    self.state.push(element);
  }

  fn squeeze(&mut self, num_bits: usize, start_with_one: bool) -> Base {
    let digest = self.digest();
    let challenge = digest_to_field(&digest, num_bits, start_with_one);
    self.state = vec![digest_to_field(
      &digest,
      challenge_capacity::<Base>(),
      false,
    )];
    challenge
  }
}

/// A SHA-256 random oracle for use inside Nova's verifier circuits.
#[derive(Serialize, Deserialize)]
pub struct Sha256ROCircuit<Base: PrimeField> {
  state: Vec<AllocatedNum<Base>>,
  constants: Sha256ROConstants,
}

fn append_constant_bytes(bits: &mut Vec<Boolean>, bytes: &[u8]) {
  for byte in bytes {
    bits.extend((0..8).rev().map(|i| Boolean::constant(byte >> i & 1 == 1)));
  }
}

fn boolean_to_allocated_bit<Base, CS>(
  mut cs: CS,
  bit: &Boolean,
) -> Result<AllocatedBit, SynthesisError>
where
  Base: PrimeField,
  CS: ConstraintSystem<Base>,
{
  if let Boolean::Is(allocated) = bit {
    return Ok(allocated.clone());
  }

  let allocated = AllocatedBit::alloc(cs.namespace(|| "allocate bit"), bit.get_value())?;
  Boolean::enforce_equal(
    cs.namespace(|| "enforce bit value"),
    &Boolean::from(allocated.clone()),
    bit,
  )?;
  Ok(allocated)
}

impl<Base: PrimeFieldBits> Sha256ROCircuit<Base> {
  fn digest<CS: ConstraintSystem<Base>>(&self, mut cs: CS) -> Result<Vec<Boolean>, SynthesisError> {
    assert!(Base::NUM_BITS as usize <= ENCODED_FIELD_BITS);
    let element_count = u64::try_from(self.state.len()).expect("RO state length fits in u64");

    let mut preimage = Vec::with_capacity(152 + self.state.len() * ENCODED_FIELD_BITS);
    append_constant_bytes(&mut preimage, &self.constants.domain);
    append_constant_bytes(&mut preimage, &[FIELD_SEQUENCE_TAG]);
    append_constant_bytes(
      &mut preimage,
      &(ENCODED_FIELD_BITS as u16 / 8).to_be_bytes(),
    );
    append_constant_bytes(&mut preimage, &element_count.to_be_bytes());

    for (element_index, element) in self.state.iter().enumerate() {
      let mut element_bits = element.to_bits_le_strict(
        cs.namespace(|| format!("decompose absorbed element {element_index}")),
      )?;
      assert!(element_bits.len() <= ENCODED_FIELD_BITS);

      preimage.extend(
        std::iter::repeat_n(
          Boolean::constant(false),
          ENCODED_FIELD_BITS - element_bits.len(),
        )
        .chain(element_bits.drain(..).rev()),
      );
    }

    sha256(cs.namespace(|| "SHA-256 random oracle"), &preimage)
  }

  fn low_digest_bits<CS: ConstraintSystem<Base>>(
    mut cs: CS,
    digest: &[Boolean],
    num_bits: usize,
    start_with_one: bool,
  ) -> Result<Vec<AllocatedBit>, SynthesisError> {
    assert_eq!(digest.len(), 256);
    assert!(num_bits <= MAX_CHALLENGE_BITS);
    assert!(num_bits < Base::NUM_BITS as usize);
    assert!(num_bits > 0 || !start_with_one);

    digest[256 - num_bits..]
      .iter()
      .rev()
      .enumerate()
      .map(|(bit_index, bit)| {
        if start_with_one && bit_index == num_bits - 1 {
          let forced = AllocatedBit::alloc(cs.namespace(|| "force challenge MSB"), Some(true))?;
          Boolean::enforce_equal(
            cs.namespace(|| "constrain challenge MSB"),
            &Boolean::from(forced.clone()),
            &Boolean::constant(true),
          )?;
          Ok(forced)
        } else {
          boolean_to_allocated_bit(cs.namespace(|| format!("challenge bit {bit_index}")), bit)
        }
      })
      .collect()
  }
}

impl<Base> ROCircuitTrait<Base> for Sha256ROCircuit<Base>
where
  Base: PrimeFieldBits + Serialize + for<'de> Deserialize<'de>,
{
  type NativeRO = Sha256RO<Base>;
  type Constants = Sha256ROConstants;

  fn new(constants: Self::Constants) -> Self {
    Self {
      state: Vec::new(),
      constants,
    }
  }

  fn absorb(&mut self, element: &AllocatedNum<Base>) {
    self.state.push(element.clone());
  }

  fn squeeze<CS: ConstraintSystem<Base>>(
    &mut self,
    mut cs: CS,
    num_bits: usize,
    start_with_one: bool,
  ) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let digest = self.digest(cs.namespace(|| "hash absorbed elements"))?;
    let challenge = Self::low_digest_bits(
      cs.namespace(|| "convert digest to challenge"),
      &digest,
      num_bits,
      start_with_one,
    )?;
    let state_bits = Self::low_digest_bits(
      cs.namespace(|| "convert digest to next state"),
      &digest,
      challenge_capacity::<Base>(),
      false,
    )?;
    self.state = vec![le_bits_to_num(
      cs.namespace(|| "pack next random-oracle state"),
      &state_bits,
    )?];
    Ok(challenge)
  }

  fn squeeze_scalar<CS: ConstraintSystem<Base>>(
    &mut self,
    mut cs: CS,
  ) -> Result<AllocatedNum<Base>, SynthesisError> {
    let digest = self.digest(cs.namespace(|| "hash absorbed elements"))?;
    let bits = Self::low_digest_bits(
      cs.namespace(|| "convert digest to scalar"),
      &digest,
      challenge_capacity::<Base>(),
      false,
    )?;
    let scalar = le_bits_to_num(cs.namespace(|| "pack digest scalar"), &bits)?;
    self.state = vec![scalar.clone()];
    Ok(scalar)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    frontend::{
      r1cs::NovaShape, shape_cs::ShapeCS, solver::SatisfyingAssignment,
      util_cs::test_cs::TestConstraintSystem, Index, Variable,
    },
    gadgets::utils::le_bits_to_num,
    provider::{
      secp_secq::{secp256k1, secq256k1},
      Secp256k1Engine,
    },
    traits::Engine,
  };
  use ff::Field;

  fn test_native_matches_circuit<Base>()
  where
    Base: PrimeFieldBits + Serialize + for<'de> Deserialize<'de>,
  {
    let constants = Sha256ROConstants::default();
    let values = [Base::from(1), -Base::ONE, Base::ROOT_OF_UNITY];
    let mut native = Sha256RO::<Base>::new(constants.clone());
    let mut circuit = Sha256ROCircuit::<Base>::new(constants);
    let mut cs = TestConstraintSystem::<Base>::new();

    for (index, value) in values.into_iter().enumerate() {
      native.absorb(value);
      let allocated =
        AllocatedNum::alloc(cs.namespace(|| format!("input {index}")), || Ok(value)).unwrap();
      circuit.absorb(&allocated);
    }

    let expected = native.squeeze(250, false);
    let result_bits = circuit
      .squeeze(cs.namespace(|| "squeeze"), 250, false)
      .unwrap();
    let result = le_bits_to_num(cs.namespace(|| "pack result"), &result_bits).unwrap();

    assert_eq!(result.get_value(), Some(expected));
    assert!(cs.is_satisfied());

    let expected_second = native.squeeze(128, true);
    let result_second_bits = circuit
      .squeeze(cs.namespace(|| "second squeeze"), 128, true)
      .unwrap();
    let result_second =
      le_bits_to_num(cs.namespace(|| "pack second result"), &result_second_bits).unwrap();

    assert_eq!(result_second.get_value(), Some(expected_second));
    assert!(cs.is_satisfied());

    let expected_empty = native.squeeze(0, false);
    let result_empty_bits = circuit
      .squeeze(cs.namespace(|| "empty squeeze"), 0, false)
      .unwrap();
    let result_empty =
      le_bits_to_num(cs.namespace(|| "pack empty result"), &result_empty_bits).unwrap();

    assert!(result_empty_bits.is_empty());
    assert_eq!(result_empty.get_value(), Some(expected_empty));
    assert!(cs.is_satisfied());

    let expected_single = native.squeeze(1, true);
    let result_single_bits = circuit
      .squeeze(cs.namespace(|| "single-bit squeeze"), 1, true)
      .unwrap();
    let result_single = le_bits_to_num(
      cs.namespace(|| "pack single-bit result"),
      &result_single_bits,
    )
    .unwrap();

    assert_eq!(result_single.get_value(), Some(expected_single));
    assert_eq!(expected_single, Base::ONE);
    assert!(cs.is_satisfied());

    let expected_full = native.squeeze(MAX_CHALLENGE_BITS, false);
    let result_full_bits = circuit
      .squeeze(
        cs.namespace(|| "maximum-width squeeze"),
        MAX_CHALLENGE_BITS,
        false,
      )
      .unwrap();
    let result_full = le_bits_to_num(
      cs.namespace(|| "pack maximum-width result"),
      &result_full_bits,
    )
    .unwrap();

    assert_eq!(result_full.get_value(), Some(expected_full));
    assert!(cs.is_satisfied());

    let expected_scalar = native.squeeze(challenge_capacity::<Base>(), false);
    let result_scalar = circuit
      .squeeze_scalar(cs.namespace(|| "scalar squeeze"))
      .unwrap();

    assert_eq!(result_scalar.get_value(), Some(expected_scalar));
    assert!(cs.is_satisfied());
  }

  #[test]
  fn native_matches_circuit() {
    test_native_matches_circuit::<secp256k1::Base>();
    test_native_matches_circuit::<secp256k1::Scalar>();
    test_native_matches_circuit::<secq256k1::Base>();
    test_native_matches_circuit::<secq256k1::Scalar>();
  }

  #[test]
  fn framing_commits_to_order_and_length() {
    let constants = Sha256ROConstants::default();
    let hash = |values: &[secp256k1::Scalar]| {
      let mut ro = Sha256RO::new(constants.clone());
      for value in values {
        ro.absorb(*value);
      }
      ro.squeeze(MAX_CHALLENGE_BITS, false)
    };

    let one = secp256k1::Scalar::from(1);
    let two = secp256k1::Scalar::from(2);
    assert_ne!(hash(&[one, two]), hash(&[two, one]));
    assert_ne!(hash(&[one]), hash(&[one, secp256k1::Scalar::ZERO]));
  }

  #[test]
  fn framing_has_a_fixed_test_vector() {
    let mut ro = Sha256RO::<secp256k1::Scalar>::new(Sha256ROConstants::default());
    ro.absorb(secp256k1::Scalar::from(42));

    let expected: [u8; 32] =
      hex::decode("a937afb7135c06711997c96b8d9c8830a438957f91e6f08fb9140766aa8d8519")
        .unwrap()
        .try_into()
        .unwrap();
    assert_eq!(ro.digest(), expected);
  }

  #[test]
  fn challenge_msb_can_be_forced() {
    let mut ro = Sha256RO::<secp256k1::Scalar>::new(Sha256ROConstants::default());
    ro.absorb(secp256k1::Scalar::from(42));
    let challenge = ro.squeeze(128, true).to_le_bits();
    assert!(challenge[127]);
  }

  fn synthesize_forced_msb<CS>(cs: &mut CS) -> Variable
  where
    CS: ConstraintSystem<<Secp256k1Engine as Engine>::Scalar>,
  {
    type Scalar = <Secp256k1Engine as Engine>::Scalar;

    let digest = vec![Boolean::constant(false); 256];
    Sha256ROCircuit::<Scalar>::low_digest_bits(cs.namespace(|| "force MSB"), &digest, 8, true)
      .unwrap()[7]
      .get_variable()
  }

  #[test]
  fn forced_msb_rejects_a_false_witness() {
    type Scalar = <Secp256k1Engine as Engine>::Scalar;

    let mut shape_cs = ShapeCS::<Secp256k1Engine>::new();
    let forced_variable = synthesize_forced_msb(&mut shape_cs);
    let shape = shape_cs.r1cs_shape().unwrap();

    let mut witness_cs = SatisfyingAssignment::<Secp256k1Engine>::new();
    let witness_variable = synthesize_forced_msb(&mut witness_cs);
    assert_eq!(forced_variable, witness_variable);

    let forced_index = match forced_variable.get_unchecked() {
      Index::Aux(index) => index,
      Index::Input(_) => panic!("forced bit must be an auxiliary variable"),
    };
    let mut assignment = witness_cs.aux_assignment().to_vec();
    assignment.push(Scalar::ONE);

    let is_satisfied = |assignment: &[Scalar]| {
      let (a, b, c) = shape.multiply_vec(assignment).unwrap();
      a.iter()
        .zip(b.iter())
        .zip(c.iter())
        .all(|((a, b), c)| *a * b == *c)
    };
    assert!(is_satisfied(&assignment));

    assignment[forced_index] = Scalar::ZERO;
    assert!(!is_satisfied(&assignment));
  }
}
