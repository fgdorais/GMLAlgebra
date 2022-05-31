import GMLAlgebra.Basic

namespace Algebra
variable {α} {β : α → α → Sort _}

class Semicategory (s : SemicategorySig β) : Prop where
  protected dop_assoc {{a b c d}} (x : β c d) (y : β b c) (z : β a b) : s.op (s.op x y) z = s.op x (s.op y z)

protected def Semicategory.infer (s : SemicategorySig β) [DOpAssoc s.op] : Semicategory s where
  dop_assoc := dop_assoc _

namespace Semicategory
variable {s : SemicategorySig β} [Semicategory s]

instance : DOpAssoc (no_index s.op) := ⟨Semicategory.dop_assoc⟩

--instance (a : α) : OpAssoc (no_index (s.toSemigroupSig a).op) := ⟨dop_assoc _ (a:=a) (b:=a) (c:=a) (d:=a)⟩

--instance (a : α) : Semigroup (no_index s.toSemigroupSig a) := Semigroup.infer _

end Semicategory

class CancelSemicategory (s : SemicategorySig β) extends Semicategory (no_index s) : Prop where
  protected dop_left_cancel {{a b c}} (x : β b c) {y z : β a b} : s.op x y = s.op x z → y = z
  protected dop_right_cancel {{a b c}} (x : β a b) {y z : β b c} : s.op y x = s.op z x → y = z

namespace CancelSemicategory
variable {s : SemicategorySig β} [CancelSemicategory s]

instance : DOpLeftCancel (no_index s.op) := ⟨CancelSemicategory.dop_left_cancel⟩
instance : DOpRightCancel (no_index s.op) := ⟨CancelSemicategory.dop_right_cancel⟩

--local instance (a : α) : OpLeftCancel (no_index (s.toSemigroupSig a).op) := ⟨dop_left_cancel _ (a:=a) (b:=a) (c:=a)⟩
--local instance (a : α) : OpRightCancel (no_index (s.toSemigroupSig a).op) := ⟨dop_right_cancel _ (a:=a) (b:=a) (c:=a)⟩

--instance (a : α) : CancelSemigroup (no_index s.toSemigroupSig a) := CancelSemigroup.infer _

end CancelSemicategory

end Algebra
