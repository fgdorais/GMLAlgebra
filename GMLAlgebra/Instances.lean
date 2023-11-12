import GMLInit
import GMLAlgebra.Signatures
import GMLAlgebra.Identities
import GMLAlgebra.UnitalRig
import GMLAlgebra.UnitalRing
import GMLAlgebra.UnitalSemiring

section instances
open Algebra

protected def Pos.sig : UnitalSemiringSig Pos where
  add := Pos.add
  mul := Pos.mul
  one := Pos.one

instance : OfNat Pos (nat_lit 1) := ⟨Pos.sig.one⟩
instance : Add Pos := ⟨Pos.sig.add⟩
instance : Mul Pos := ⟨Pos.sig.mul⟩

instance Pos.instUnitalCommSemiring : UnitalCommSemiring Pos.sig where
  add_assoc := Pos.add_assoc
  add_comm := Pos.add_comm
  mul_assoc := Pos.mul_assoc
  mul_comm := Pos.mul_comm
  mul_right_id := Pos.mul_one
  mul_right_distrib := Pos.right_distrib

protected def Nat.sig : UnitalRigSig Nat where
  add := Nat.add
  mul := Nat.mul
  zero := Nat.zero
  one := Nat.succ Nat.zero

instance : OfNat Nat (nat_lit 0) := ⟨Nat.sig.zero⟩
instance : OfNat Nat (nat_lit 1) := ⟨Nat.sig.one⟩
instance : Add Nat := ⟨Nat.sig.add⟩
instance : Mul Nat := ⟨Nat.sig.mul⟩

instance Nat.instUnitalCommRig : UnitalCommRig Nat.sig where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  add_right_id := Nat.add_zero
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  mul_right_id := Nat.mul_one
  mul_right_distrib := Nat.right_distrib
  mul_right_zero := Nat.mul_zero

protected def Int.sig : UnitalRingSig Int where
  add := Int.add
  mul := Int.mul
  neg := Int.neg
  zero := Int.ofNat 0
  one := Int.ofNat 1

instance : OfNat Int (nat_lit 0) := ⟨Int.sig.zero⟩
instance : OfNat Int (nat_lit 1) := ⟨Int.sig.one⟩
instance : Add Int := ⟨Int.sig.add⟩
instance : Neg Int := ⟨Int.sig.neg⟩
instance : Mul Int := ⟨Int.sig.mul⟩

instance Int.instUnitalCommRing : UnitalCommRing Int.sig where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_right_id := Int.add_zero
  add_right_inv := Int.add_neg_self_right
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  mul_right_id := Int.mul_one
  mul_right_distrib := Int.add_mul

end instances
