/- "Proving in the Large" chapter of CPDT -/

inductive exp : Type
| Const (n : nat) : exp
| Plus (e1 e2 : exp) : exp
| Mult (e1 e2 : exp) : exp

open exp

def eeval : exp → nat
| (Const n)    := n
| (Plus e1 e2) := eeval e1 + eeval e2
| (Mult e1 e2) := eeval e1 * eeval e2

def times (k : nat) : exp → exp
| (Const n)    := Const (k * n)
| (Plus e1 e2) := Plus (times e1) (times e2)
| (Mult e1 e2) := Mult (times e1) e2

def reassoc : exp → exp
| (Const n)    := (Const n)
| (Plus e1 e2) :=
  let e1' := reassoc e1 in
  let e2' := reassoc e2 in
  match e2' with
  | (Plus e21 e22) := Plus (Plus e1' e21) e22
  | _              := Plus e1' e2'
  end
| (Mult e1 e2) :=
  let e1' := reassoc e1 in
  let e2' := reassoc e2 in
  match e2' with
  | (Mult e21 e22) := Mult (Mult e1' e21) e22
  | _              := Mult e1' e2'
  end

class semiring (α : Type) extends has_mul α, has_add α, has_one α, has_zero α.

instance foo : semiring nat :=
{ zero := 0, one := 1, add := (+), mul := (*) }

variables {α : Type} [semiring α] (a b c : α)

lemma left_distrib : a * (b + c) = a * b + a * c := sorry
lemma right_distrib : (a + b) * c = a * c + b * c := sorry
lemma mul_comm : a * b = b * a := sorry
lemma mul_assoc : a * b * c = a * (b * c) := sorry
lemma mul_left_comm : a * (b * c) = b * (a * c) := sorry

attribute [simp] left_distrib right_distrib times reassoc eeval mul_comm mul_assoc mul_left_comm

theorem eeval_times (k e) : eeval (times k e) = k * eeval e :=
by induction e; simp [*]

set_option trace.smt true

theorem reassoc_correct (e) : eeval (reassoc e) = eeval e :=
by induction e; simp [*]; cases (reassoc e_e2); rsimp
