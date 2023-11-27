mod circuit;
mod Expression;
mod table;

use core::{
    fmt::Debug,
    ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign},
};
use ff::{PrimeField, PrimeFieldBits};

use serde::{Deserialize, Serialize};

/// Represents an element of a group
/// This is currently tailored for an elliptic curve group
pub trait Group:
    Clone
    + Copy
    + Debug
    + Eq
    + GroupOps
    + GroupOpsOwned
    + ScalarMul<<Self as Group>::Scalar>
    + ScalarMulOwned<<Self as Group>::Scalar>
    + Send
    + Sync
    + Serialize
    + for<'de> Deserialize<'de>
{
    /// A type representing an element of the base field of the group
    type Base: PrimeFieldBits + TranscriptReprTrait<Self> + Serialize + for<'de> Deserialize<'de>;

    /// A type representing an element of the scalar field of the group
    type Scalar: PrimeFieldBits
    + PrimeFieldExt
    + Send
    + Sync
    + TranscriptReprTrait<Self>
    + Serialize
    + for<'de> Deserialize<'de>;

    /// A type representing the compressed version of the group element
    type CompressedGroupElement: CompressedGroup<GroupElement = Self>;


}

/// A helper trait for types with a group operation.
pub trait GroupOps<Rhs = Self, Output = Self>:
Add<Rhs, Output = Output> + Sub<Rhs, Output = Output> + AddAssign<Rhs> + SubAssign<Rhs>
{
}

impl<T, Rhs, Output> GroupOps<Rhs, Output> for T where
    T: Add<Rhs, Output = Output> + Sub<Rhs, Output = Output> + AddAssign<Rhs> + SubAssign<Rhs>
{
}

/// A helper trait for references with a group operation.
pub trait GroupOpsOwned<Rhs = Self, Output = Self>: for<'r> GroupOps<&'r Rhs, Output> {}
impl<T, Rhs, Output> GroupOpsOwned<Rhs, Output> for T where T: for<'r> GroupOps<&'r Rhs, Output> {}

/// A helper trait for types implementing group scalar multiplication.
pub trait ScalarMul<Rhs, Output = Self>: Mul<Rhs, Output = Output> + MulAssign<Rhs> {}

impl<T, Rhs, Output> ScalarMul<Rhs, Output> for T where T: Mul<Rhs, Output = Output> + MulAssign<Rhs>
{}

/// A helper trait for references implementing group scalar multiplication.
pub trait ScalarMulOwned<Rhs, Output = Self>: for<'r> ScalarMul<&'r Rhs, Output> {}
impl<T, Rhs, Output> ScalarMulOwned<Rhs, Output> for T where T: for<'r> ScalarMul<&'r Rhs, Output> {}
