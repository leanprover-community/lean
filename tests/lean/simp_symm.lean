constants f g : nat → nat

-- Test `simp` with lemmas in reverse direction
axiom f_id : ∀ x, f x = x
axiom f_g : ∀ x, f x = g x
example (a : nat) : g a = a :=
by simp [←f_g, f_id] -- works
-- Alternate syntax:
example (a : nat) : g a = a :=
by simp [<-f_g, f_id] -- works

-- Universe polymorphic lemmas work:
universe u
variable {α : Type u}
constants fu gu : α → α
axiom fu_id : ∀ (x : α), fu x = id x
axiom fu_gu : ∀ (x : α), fu x = gu x
example (a : nat) : gu a = a :=
by simp [←fu_gu, fu_id] -- works

-- Reverse direction also works for `↔`
constants p q : α → Prop
axiom pq : ∀ (x : α), p x ↔ q x
example (a : nat) (h : p a) : q a :=
by { simp [←pq], assumption }

section reverse_conflict
open interactive
open tactic.interactive
open tactic.simp_arg_type

def op : nat → nat → nat := sorry
@[simp] lemma op_assoc (a b c : nat) : op (op a b) c = op a (op b c) := sorry

-- Passing an existing `@[simp]` lemma in reverse direction works:
-- The failure case is that the existing lemma isn't deleted from the set,
-- so the simplifier goes in an infinite loop.
-- We prevent that with the `try_for` call.
example (a b c : nat) (h : p (op (op a b) c)) : p (op a (op b c)) :=
by λ s, match try_for 1000 (simp none ff [symm_expr ``(op_assoc)] [] (loc.ns [none]) {} s) with
        | none := result.exception (some (λ _, format!"timeout in try_for")) none s
        | (some (result.success _ s')) := assumption s'
        | (some exception) := exception
        end
end reverse_conflict
