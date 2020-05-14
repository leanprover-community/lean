class ring (α : Type*) extends has_zero α, has_add α, has_one α, has_mul α.

lemma add_comm {α : Type*} [ring α] (a b : α) : a + b = b + a := sorry

lemma {u} ring_add_comm {α : Type u} [ring α] : ∀ (a b : α), (: a + b :) = b + a :=
add_comm

open smt_tactic
meta def no_ac : smt_config :=
{ cc_cfg := { ac := ff }}

class field (α : Type*) extends ring α, has_inv α.

lemma ex {α : Type} [field α] (a b : α) : a + b = b + a :=
begin [smt] with no_ac,
  ematch_using [ring_add_comm]
end
