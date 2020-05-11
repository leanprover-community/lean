inductive imf (f : nat → nat) : nat → Type
| mk1 : ∀ (a : nat), imf (f a)
| mk2 : imf (f 0 + 1)

definition inv_2 (f : nat → nat) : ∀ (b : nat), imf f b → {x : nat // x > b} → nat
| _ (imf.mk1 a) x := a
| _ imf.mk2     x := subtype.val x
