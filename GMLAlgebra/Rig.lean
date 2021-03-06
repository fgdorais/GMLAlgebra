import GMLAlgebra.Basic
import GMLAlgebra.Group
import GMLAlgebra.Monoid
import GMLAlgebra.Semigroup
import GMLAlgebra.UnitalSemiring

namespace Algebra
variable {Î±} (s : RigSig Î±)

local infixr:70 " â " => s.mul
local infixr:65 " â¹ " => s.add
local notation "ð" => s.zero

class Rig extends Semiring (no_index s.toSemiringSig) : Prop where
  protected add_right_id (x) : x â¹ ð = x
  protected mul_left_zero (x) : ð â x = ð
  protected mul_right_zero (x) : x â ð = ð

protected def Rig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] [OpLeftNil s.mul s.zero] [OpRightNil s.mul s.zero] : Rig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _
  mul_left_zero := op_left_nil _
  mul_right_zero := op_right_nil _

namespace Rig
variable {s} [self : Rig s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := â¨Rig.add_right_idâ©
instance : OpLeftNil (no_index s.mul) (no_index s.zero) := â¨Rig.mul_left_zeroâ©
instance : OpRightNil (no_index s.mul) (no_index s.zero) := â¨Rig.mul_right_zeroâ©

instance toAddCommMonoid : CommMonoid (no_index s.toAddMonoidSig) := CommMonoid.infer _

end Rig

class CommRig extends CommSemiring (no_index s.toSemiringSig): Prop where
  protected add_right_id (x) : x â¹ ð = x
  protected mul_right_zero (x) : x â ð = ð

protected def CommRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] [OpRightNil s.mul s.zero] : CommRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _
  mul_right_zero := op_right_nil _

namespace CommRig
variable {s} [self : CommRig s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := â¨CommRig.add_right_idâ©
local instance : OpRightNil (no_index s.mul) (no_index s.zero) := â¨CommRig.mul_right_zeroâ©

protected theorem mul_left_zero (x) : ð â x = ð := calc
  _ = x â ð := by rw [op_comm (.â.) x ð]
  _ = ð := by rw [op_right_nil (.â.) x]
local instance : OpLeftNil (no_index s.mul) (no_index s.zero) := â¨CommRig.mul_left_zeroâ©

instance toRig : Rig s := Rig.infer s

end CommRig

class CancelRig extends Semiring (no_index s.toSemiringSig) : Prop where
  protected add_right_id (x) : x â¹ ð = x
  protected add_right_cancel (x) {y z} : y â¹ x = z â¹ x â y = z

protected def CancelRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpRightCancel s.add] [OpAssoc s.mul] [OpLeftDistrib s.mul s.add] [OpRightDistrib s.mul s.add] : CancelRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  add_right_cancel := op_right_cancel _
  mul_assoc := op_assoc _
  mul_left_distrib := op_left_distrib _
  mul_right_distrib := op_right_distrib _

namespace CancelRig
variable {s} [self : CancelRig s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := â¨CancelRig.add_right_idâ©
local instance : OpRightCancel (no_index s.add) := â¨CancelRig.add_right_cancelâ©

instance toAddCancelCommMonoid : CancelCommMonoid (no_index s.toAddMonoidSig) := CancelCommMonoid.infer _

protected theorem mul_left_zero (x) : ð â x = ð :=
  op_right_cancel (.â¹.) (ð â x) $ calc
  _ = (ð â¹ ð) â x := by rw [op_right_distrib (.â.) ð ð x]
  _ = ð â x := by rw [op_right_id (.â¹.) ð]
  _ = ð â¹ ð â x := by rw [op_left_id (.â¹.)]
local instance : OpLeftNil (no_index s.mul) (no_index s.zero) := â¨CancelRig.mul_left_zeroâ©

protected theorem mul_right_zero (x) : x â ð = ð :=
  op_right_cancel (.â¹.) (x â ð) $ calc
  _ = x â (ð â¹ ð) := by rw [op_left_distrib (.â.) x ð ð]
  _ = x â ð := by rw [op_right_id (.â¹.) ð]
  _ = ð â¹ x â ð := by rw [op_left_id (.â¹.)]
local instance : OpRightNil (no_index s.mul) (no_index s.zero) := â¨CancelRig.mul_right_zeroâ©

instance toRig : Rig s := Rig.infer s

end CancelRig

class CancelCommRig extends CommSemiring (no_index s.toSemiringSig) : Prop where
  protected add_right_id (x) : x â¹ ð = x
  protected add_right_cancel (x) {y z} : y â¹ x = z â¹ x â y = z

protected def CancelCommRig.infer [OpAssoc s.add] [OpComm s.add] [OpRightId s.add s.zero] [OpRightCancel s.add] [OpAssoc s.mul] [OpComm s.mul] [OpRightDistrib s.mul s.add] : CancelCommRig s where
  add_assoc := op_assoc _
  add_comm := op_comm _
  add_right_id := op_right_id _
  add_right_cancel := op_right_cancel _
  mul_assoc := op_assoc _
  mul_comm := op_comm _
  mul_right_distrib := op_right_distrib _

namespace CancelCommRig
variable {s} [self : CancelCommRig s]

local instance : OpRightId (no_index s.add) (no_index s.zero) := â¨CancelCommRig.add_right_idâ©
local instance : OpRightCancel (no_index s.add) := â¨CancelCommRig.add_right_cancelâ©

instance toCancelRig : CancelRig s := CancelRig.infer s

instance toCommRig : CommRig s := CommRig.infer s

end CancelCommRig

end Algebra
