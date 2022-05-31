import GMLAlgebra.Basic
import GMLAlgebra.Semicategory

namespace Algebra
variable {α} {β : α → α → Sort _}

class Category (s : CategorySig β) extends Semicategory (no_index s.toSemicategorySig): Prop where
  protected dop_left_id {{a b}} (x : β a b) : s.op s.id x = x
  protected dop_right_id {{a b}} (x : β a b) : s.op x s.id = x

protected def Category.infer (s : CategorySig β) [DOpAssoc s.op] [DOpLeftId s.op s.id] [DOpRightId s.op s.id] : Category s where
  dop_assoc := dop_assoc _
  dop_left_id := dop_left_id _
  dop_right_id := dop_right_id _

namespace Category
variable {s : CategorySig β} [Category s]

instance : DOpLeftId (no_index s.op) (no_index s.id) := ⟨Category.dop_left_id⟩
instance : DOpRightId (no_index s.op) (no_index s.id) := ⟨Category.dop_right_id⟩

instance (a : α) : OpLeftId (no_index (s.toMonoidSig a).op) (no_index (s.toMonoidSig a).id) := ⟨dop_left_id (a:=a) (b:=a) _⟩
instance (a : α) : OpRightId (no_index (s.toMonoidSig a).op) (no_index (s.toMonoidSig a).id) := ⟨dop_right_id (a:=a) (b:=a) _⟩

--instance (a : α) : Monoid (no_index s.toMonoidSig a) := Monoid.infer _

end Category

class CancelCategory (s : CategorySig β) extends Category (no_index s), CancelSemicategory (no_index s.toSemicategorySig) : Prop

protected def CancelCategory.infer (s : CategorySig β) [DOpAssoc s.op] [DOpLeftId s.op s.id] [DOpRightId s.op s.id] [DOpLeftCancel s.op] [DOpRightCancel s.op] : CancelCategory s where
  dop_assoc := dop_assoc _
  dop_left_id := dop_left_id _
  dop_right_id := dop_right_id _
  dop_left_cancel := dop_left_cancel _
  dop_right_cancel := dop_right_cancel _

namespace CancelCategory
variable {s : CategorySig β} [CancelCategory s]

instance (a : α) : OpLeftCancel (no_index (s.toMonoidSig a).op) := ⟨dop_left_cancel (a:=a) (b:=a) (c:=a) _⟩
instance (a : α) : OpRightCancel (no_index (s.toMonoidSig a).op) := ⟨dop_right_cancel (a:=a) (b:=a) (c:=a) _⟩

--instance (a : α) : CancelMonoid (no_index s.toMonoidSig a) := CancelMonoid.infer _

end CancelCategory

end Algebra
