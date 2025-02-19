import GMLAlgebra.Basic
import GMLAlgebra.Instances
import GMLAlgebra.Semigroup

open List
open Logic

namespace Algebra

namespace Semigroup

inductive Expr {α} (xs : List α)
| var : Index xs → Expr xs
| app : Expr xs → Index xs → Expr xs

namespace Expr
variable {α} {xs : List α}

instance instDecidableEq : DecidableEq (Expr xs)
| var i, var j =>
  match inferDecidable (i = j) with
  | isTrue rfl => isTrue rfl
  | isFalse h => isFalse fun | rfl => h rfl
| var _, app _ _ => isFalse Expr.noConfusion
| app _ _, var _ => isFalse Expr.noConfusion
| app a i, app b j =>
  match instDecidableEq a b, inferDecidable (i = j) with
  | isTrue rfl, isTrue rfl => isTrue rfl
  | _, isFalse h => isFalse fun | rfl => h rfl
  | isFalse h, _ => isFalse fun | rfl => h rfl

def lift (x : α) : Expr xs → Expr (x :: xs)
| var i => var (Index.tail i)
| app a i => app (lift x a) (Index.tail i)

def op : Expr xs → Expr xs → Expr xs
| a, var i => app a i
| a, app b i => app (op a b) i

section Eval
variable (s : SemigroupSig α)

def eval {xs : List α} : Expr xs → α
| var i => i.val
| app a i => s.op (eval a) i.val


@[simp] theorem eval_lift (x) {xs} : ∀ (a : Expr xs), eval s (lift x a) = eval s a
| var i => by simp [lift, eval]
| app a i => by simp [lift, eval, eval_lift x a]

@[simp] theorem eval_app {xs} (a : Expr xs) (i : Index xs) : eval s (app a i) = s.op (eval s a) i.val := rfl

@[simp] theorem eval_var {xs} (i : Index xs) : eval s (var i) = i.val := rfl

@[simp] theorem eval_op [Semigroup s] {xs} : ∀ (a b : Expr xs), eval s (op a b) = s.op (eval s a) (eval s b)
| a, var i => rfl
| a, app b i => by simp only [eval, op, eval_op, op_assoc s.op]

end Eval

section Completeness
variable (xs : List α)

def sig : SemigroupSig (Expr xs) where
  op := Expr.op

protected theorem op_assoc : ∀ (a b c : Expr xs), op (op a b) c = op a (op b c)
| _, _, var _ => rfl
| a, b, app c k => by simp [op, Expr.op_assoc a b c]

instance : Semigroup (Expr.sig xs) where
  op_assoc := Expr.op_assoc xs

end Completeness

end Expr

class Reflect (s : SemigroupSig α) (x : α) (xs : List α) where
  expr : Expr xs
  eval_eq : expr.eval s = x

protected def Reflect.eq (s : SemigroupSig α) (x xs) [inst : Reflect s x xs] : inst.expr.eval s = x := inst.eval_eq

namespace Reflect
variable (s : SemigroupSig α) [Semigroup s]

class Var (x : α) (xs : List α) extends Reflect s x xs

instance (priority:=low) instVarLift (x y : α) (xs : List α) [Var s y xs] : Var s y (x :: xs) where
  expr := Expr.lift x (expr s y)
  eval_eq := by simp [eval_eq]

instance instVarSelf (x : α) (xs : List α) : Var s x (x :: xs) where
  expr := Expr.var Index.head
  eval_eq := by simp

instance instOp (x y : α) {xs : List α} [Reflect s x xs] [Reflect s y xs] : Reflect s (no_index (s.op x y)) xs where
  expr := Expr.op (expr s x) (expr s y)
  eval_eq := by simp [eval_eq]

end Reflect

theorem reflect {α} (s : SemigroupSig α) [Semigroup s] (xs : List α) {a b : α} [Reflect s a xs] [Reflect s b xs] : Reflect.expr s a (xs:=xs) = Reflect.expr s b → a = b := by
  intro h
  rw [←Reflect.eq s a xs, ←Reflect.eq s b xs, h]

end Semigroup

end Algebra

section Example
open Algebra Notation
variable {α : Type _} (s : SemigroupSig α) [Semigroup s] (a b c d : α)

local infix:70 " ⋆ " => s.op

example : (a ⋆ b) ⋆ (c ⋆ d) = a ⋆ ((b ⋆ c) ⋆ d) :=
  Semigroup.reflect s [a,b,c,d] rfl

example (x y z : Pos) : 1 + (x + y) + (z + y) = (1 + x + (y + z)) + y :=
  Semigroup.reflect Pos.sig.toAddSemigroupSig [1,x,y,z] rfl

end Example
