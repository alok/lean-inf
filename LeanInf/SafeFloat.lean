import Mathlib
import Lean.Data.Json
-- TODO bind to crates in rust directly
/-!
This module implements a safe wrapper around `Float` to ensure that
all operations are well-defined. It is based on Rust's ordered_float crate.
-/


-- masks for the parts of the IEEE 754 float
def SIGN_MASK: UInt64 := 0x8000000000000000
def EXP_MASK: UInt64 := 0x7ff0000000000000
def MAN_MASK: UInt64 := 0x000ffffffffffff

-- canonical raw bit patterns (for hashing)
def CANONICAL_NAN_BITS: UInt64 := 0x7ff8000000000000



def canonicalize_signed_zero (x: Float) : Float :=
    --0.0 + 0.0 == +0.0 under IEEE754 roundTiesToEven rounding mode,
    -- which Rust guarantees. Thus by adding a positive zero we
    -- canonicalize signed zero without any branches in one instruction.
    x + (0.0: Float)
#eval -0.0 + 0.0
#eval canonicalize_signed_zero (-0.0)


structure OrderedFloat where
  data: Float
deriving Repr, Inhabited--,ToJson,FromJson

instance : OfScientific OrderedFloat where
  ofScientific man exp dec := ⟨Float.ofScientific man exp dec⟩

def OrderedFloat.into_inner (self: OrderedFloat) : Float := match self with
  | ⟨val⟩ => val

instance : Ord OrderedFloat where
  compare := fun self other =>
    if self.data.isNaN then
      if other.data.isNaN then
        Ordering.eq
      else
        Ordering.lt
    else
      if self.data - other.data > 0 then
        Ordering.gt
      else if self.data - other.data < 0 then
        Ordering.lt
      else
        Ordering.eq

instance : LT OrderedFloat where
  lt self other := match compare self other with
    | Ordering.lt => true
    | _ => false

instance : BEq OrderedFloat where
  beq := fun self other =>
    if self.data.isNaN then
      other.data.isNaN
    else
      self.data == other.data

instance : LE OrderedFloat where
  le self other := if self.data.isNaN then true else self.data <= other.data
#eval Ord.compare (1.8:OrderedFloat) (9.3:OrderedFloat)


-- #eval (1.8:OrderedFloat)<=(9.3:OrderedFloat)


instance : Hashable OrderedFloat where
  hash self :=
    if self.data.isNaN then
      CANONICAL_NAN_BITS
    else
      self.data.toUInt64



instance : Coe Float OrderedFloat where
  coe x := ⟨x⟩


instance : Coe Bool Nat where
  coe x := if x then 1 else 0

instance : OfNat Bool n where
  ofNat := n > 0

instance : Coe Nat OrderedFloat where
  coe x := ⟨Float.ofNat x⟩

#eval (1.2:OrderedFloat)
#eval ((1:Bool):OrderedFloat)


instance : Add OrderedFloat where
  add x y := ⟨x.data + y.data⟩

instance : Sub OrderedFloat where
  sub x y := ⟨x.data - y.data⟩

instance : Mul OrderedFloat where
  mul x y := ⟨x.data * y.data⟩

instance : Div OrderedFloat where
  div x y := ⟨x.data / y.data⟩
instance : Inv OrderedFloat where
  inv x := ⟨1 / x.data⟩

/-- exponentiation by squaring -/
instance : Pow OrderedFloat Nat where
  pow x n := Id.run do
    let mut base := x
    let mut exp := n
    let mut result := ⟨1⟩
    while exp > 0 do
      if exp % 2 == 1 then
        result := result * base
      base := base * base
      exp := exp / 2
    return result

instance : Pow OrderedFloat Float where
  pow x n := ⟨x.data ^ n⟩

#eval ((2.3 - 3.3):OrderedFloat)+(3.0:Float)

def Float.signum (x: Float) : Float :=
  if x > 0 then 1.0 else if x < 0 then -1.0 else 0.0

instance : ToString OrderedFloat where
  toString x := x.data.toString

instance : Neg OrderedFloat where
  neg x := ⟨-x.data⟩

instance : Zero OrderedFloat where
  zero := ⟨0.0⟩

instance : One OrderedFloat where
  one := ⟨1.0⟩

def OrderedFloat.nan : OrderedFloat := ⟨Float.nan⟩
def OrderedFloat.infinity : OrderedFloat := ⟨Float.inf⟩
def OrderedFloat.neg_infinity : OrderedFloat := ⟨-Float.inf⟩
def OrderedFloat.neg_zero : OrderedFloat := ⟨0.0⟩

def OrderedFloat.isNan (x : OrderedFloat) : Bool := x.data.isNaN


def OrderedFloat.isInf (x : OrderedFloat) : Bool := x.data.isInf

def OrderedFloat.isFinite (x : OrderedFloat) : Bool := x.data.isFinite


def OrderedFloat.floor (x : OrderedFloat) : OrderedFloat := ⟨x.data.floor⟩

def OrderedFloat.ceil (x : OrderedFloat) : OrderedFloat := ⟨x.data.ceil⟩
def OrderedFloat.round (x : OrderedFloat) : OrderedFloat := ⟨x.data.round⟩


def OrderedFloat.abs (x : OrderedFloat) : OrderedFloat := ⟨x.data.abs⟩
def OrderedFloat.signum (x : OrderedFloat) : OrderedFloat := ⟨x.data.signum⟩

def OrderedFloat.acos (x : OrderedFloat) : OrderedFloat := ⟨x.data.acos⟩
def OrderedFloat.asin (x : OrderedFloat) : OrderedFloat := ⟨x.data.asin⟩
def OrderedFloat.atan (x : OrderedFloat) : OrderedFloat := ⟨x.data.atan⟩
def OrderedFloat.atan2 (x : OrderedFloat) (y : OrderedFloat) : OrderedFloat := ⟨x.data.atan2 y.data⟩
def OrderedFloat.cos (x : OrderedFloat) : OrderedFloat := ⟨x.data.cos⟩
def OrderedFloat.sin (x : OrderedFloat) : OrderedFloat := ⟨x.data.sin⟩
def OrderedFloat.tan (x : OrderedFloat) : OrderedFloat := ⟨x.data.tan⟩
def OrderedFloat.cosh (x : OrderedFloat) : OrderedFloat := ⟨x.data.cosh⟩
def OrderedFloat.sinh (x : OrderedFloat) : OrderedFloat := ⟨x.data.sinh⟩
def OrderedFloat.tanh (x : OrderedFloat) : OrderedFloat := ⟨x.data.tanh⟩
def OrderedFloat.exp (x : OrderedFloat) : OrderedFloat := ⟨x.data.exp⟩
def OrderedFloat.exp2 (x : OrderedFloat) : OrderedFloat := ⟨x.data.exp2⟩
def OrderedFloat.log (x : OrderedFloat) : OrderedFloat := ⟨x.data.log⟩
def OrderedFloat.log2 (x : OrderedFloat) : OrderedFloat := ⟨x.data.log2⟩
def OrderedFloat.log10 (x : OrderedFloat) : OrderedFloat := ⟨x.data.log10⟩
def OrderedFloat.sqrt (x : OrderedFloat) : OrderedFloat := ⟨x.data.sqrt⟩
def OrderedFloat.cbrt (x : OrderedFloat) : OrderedFloat := ⟨x.data.cbrt⟩



-- Tests for OrderedFloat and related functions

#eval do
  let float := OrderedFloat.mk 1.0
  let float2 := OrderedFloat.mk 1.0
  IO.println s!"OrderedFloat test: {float == float2}"

#eval do
  let float := OrderedFloat.mk 1.0
  IO.println s!"NotNan test: {!float.isNan}"

#eval do
  let nanFloat := OrderedFloat.nan
  IO.println s!"Fail on NaN test: {nanFloat.isNan}"

#eval do
  let infFloat := OrderedFloat.infinity
  IO.println s!"Infinity test: {infFloat.isInf}"

#eval do
  let negInfFloat := OrderedFloat.neg_infinity
  IO.println s!"Negative infinity test: {negInfFloat.isInf}"

#eval do
  let zeroFloat : OrderedFloat := 0
  IO.println s!"Zero test: {zeroFloat == OrderedFloat.mk 0.0}"

#eval do
  let oneFloat : OrderedFloat := 1
  IO.println s!"One test: {oneFloat == OrderedFloat.mk 1.0}"

#eval do
  let negFloat := OrderedFloat.mk (-5.0)
  IO.println s!"Abs test: {negFloat.abs == OrderedFloat.mk 5.0}"

#eval do
  let float := OrderedFloat.mk 3.7
  IO.println s!"Floor test: {float.floor == OrderedFloat.mk 3.0}"

#eval do
  let float := OrderedFloat.mk 3.2
  IO.println s!"Ceil test: {float.ceil == OrderedFloat.mk 4.0}"

#eval do
  let float := OrderedFloat.mk 3.5
  IO.println s!"Round test: {float.round == OrderedFloat.mk 4.0}"
