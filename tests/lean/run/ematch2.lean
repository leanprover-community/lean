class add_comm_monoid (α : Type*) extends has_zero α, has_add α.

section
variables {α : Type*} [add_comm_monoid α] (a b c : α)

lemma add_assoc : a + b + c = a + (b + c) := sorry
lemma add_comm : a + b = b + a := sorry

instance aa : is_associative α (+) := ⟨sorry⟩
instance ac : is_commutative α (+) := ⟨sorry⟩

end

namespace foo
universe variables u
variables {α : Type u}

open tactic

meta def add_insts : list (expr × expr) → tactic unit
| []              := skip
| ((inst, pr)::r) := do
  assertv `_einst inst pr,
  add_insts r

meta def internalize_hs : list expr → ematch_state → tactic ematch_state
| []      s := return s
| (h::hs) s := do t ← infer_type h, s ← s^.internalize t, internalize_hs hs s

meta def ematch_test (h : name) : tactic unit :=
do cc  ← cc_state.mk_using_hs,
   ctx ← local_context,
   ems ← internalize_hs ctx (ematch_state.mk {}),
   tgt ← target,
   ems ← ems^.internalize tgt,
   hlemma ← hinst_lemma.mk_from_decl h,
   (r, cc, ems) ← ematch_all cc ems hlemma tt,
   add_insts r

section
variables [add_comm_monoid α]

theorem add_comm_three  (a b c : α) : a + b + c = c + b + a :=
begin ematch_test `add_comm, ematch_test `add_assoc, cc end

theorem add.comm4 : ∀ (n m k l : α), n + m + (k + l) = n + k + (m + l) :=
by cc

end
end foo
