namespace imp
open tactic

@[reducible]
def uname := string

inductive aexp
| val   : nat → aexp
| var   : uname → aexp
| plus  : aexp → aexp → aexp
| times : aexp → aexp → aexp

instance : decidable_eq aexp :=
by mk_dec_eq_instance

@[reducible]
def value := nat

def state := uname → value

open aexp

def aval : aexp → state → value
| (val n)      s := n
| (var x)      s := s x
| (plus a₁ a₂) s := aval a₁ s + aval a₂ s
| (times a₁ a₂) s := aval a₁ s * aval a₂ s

example : aval (plus (val 3) (var "x")) (λ x, 0) = 3 :=
rfl

def updt (s : state) (x : uname) (v : value) : state :=
λ y, if x = y then v else s y

def asimp_const : aexp → aexp
| (val n)      := val n
| (var x)      := var x
| (plus a₁ a₂) :=
  match asimp_const a₁, asimp_const a₂ with
  | val n₁, val n₂ := val (n₁ + n₂)
  | b₁,     b₂     := plus b₁ b₂
  end
| (times a₁ a₂) :=
  match asimp_const a₁, asimp_const a₂ with
  | val n₁, val n₂ := val (n₁ * n₂)
  | b₁,     b₂     := times b₁ b₂
  end

example : asimp_const (plus (plus (val 2) (val 3)) (var "x")) = plus (val 5) (var "x") :=
rfl

attribute [ematch] asimp_const aval

-- attribute [ematch] nat.zero_add nat.add_zero nat.mul_one nat.one_mul nat.zero_mul nat.mul_zero
--   nat.add_sub_add_left nat.add_sub_add_right min_eq_right min_eq_left
--   nat.add_sub_cancel nat.add_sub_cancel_left

set_option trace.smt.ematch true

-- set_option pp.all true

meta def not_done : tactic unit := fail_if_success done

class semiring (α : Type) extends has_zero α, has_one α, has_add α, has_mul α.

instance foo : semiring ℕ :=
{ zero := 0,
  one := 1,
  add := (+),
  mul := (*) }

section
variables {α : Type} [semiring α] (a : α)

lemma zero_add : (0:α) + a = a := sorry
lemma add_zero : a + 0 = a := sorry
lemma zero_mul : (0:α) * a = 0 := sorry
lemma mul_zero : a * 0 = 0 := sorry
lemma one_mul : (1:α) * a = a := sorry
lemma mul_one : a * 1 = a := sorry

end

attribute [ematch] zero_add add_zero mul_one zero_mul mul_zero
  nat.add_sub_add_left nat.add_sub_add_right min_eq_right min_eq_left
  nat.add_sub_cancel nat.add_sub_cancel_left

lemma aval_asimp_const (a : aexp) (s : state) : aval (asimp_const a) s = aval a s :=
begin [smt]
  smt_tactic.get_lemmas >>= smt_tactic.trace,
end


-- lemma aval_asimp_const' (a : aexp) (s : state) : aval (asimp_const a) s = aval a s :=
-- begin [smt]
--  induction a,
--  destruct (asimp_const a_a_1),
-- { destruct (asimp_const a_a),
--   { ematch, ematch,
--     smt_tactic.ematch >> smt_tactic.trace_state },
--   all_goals {admit}},
-- all_goals {admit}
-- end

lemma aval_asimp_const (a : aexp) (s : state) : aval (asimp_const a) s = aval a s :=
begin [smt]
 induction a,
 all_goals {destruct (asimp_const a_a_1), all_goals {destruct (asimp_const a_a), eblast}}
end

lemma ex2 (a : aexp) (s : state) : aval (asimp_const a) s = aval a s :=
begin [smt]
 induction a,
 all_goals {destruct (asimp_const a_a_1), all_goals {destruct (asimp_const a_a), eblast_using [asimp_const, aval]}}
end

end imp
