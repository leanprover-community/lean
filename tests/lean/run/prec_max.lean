open nat

reserve postfix ⁻¹:(max + 1)

postfix (name := symm) ⁻¹ := eq.symm

constant foo (a b : nat) : a + b = 0

theorem tst1 (a b : nat) : 0 = a + b :=
(foo _ _)⁻¹

constant f {a b : nat} (h1 : 0 = a + b) (h2 : a = b) : a = 0 ∧ b = 0

example (a b : nat) : a = 0 ∧ b = 0 :=
f (foo _ _)⁻¹ sorry

example (a b : nat) : a = 0 ∧ b = 0 :=
f (foo _ _)⁻¹ sorry⁻¹
