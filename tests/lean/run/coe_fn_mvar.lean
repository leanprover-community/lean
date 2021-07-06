structure hom (α β : Type*) := (f : α → β)

instance {α β} : has_coe_to_fun (hom α β) (λ _, α → β) := ⟨hom.f⟩

def frob {α β} (a : α) : hom β (α × β) := ⟨λ b, (a, b)⟩

-- `(frob 1 : hom ?m_1 (?m_2 × ?m_1))` has metavariables in the type
def foo : ℤ × ℤ := frob 1 2

example : foo = (1, 2) := rfl

-- backport elabissues/Reid1.lean from Lean 4

structure constantFunction (α β : Type) :=
(f : α → β)
(h : ∀ a₁ a₂, f a₁ = f a₂)

instance {α β : Type} : has_coe_to_fun (constantFunction α β) (λ _, α → β) :=
⟨constantFunction.f⟩

def myFun {α : Type} : constantFunction α (option α) :=
{ f := fun a, none,
  h := fun a₁ a₂, rfl }

def myFun' (α : Type) : constantFunction α (option α) :=
{ f := fun a, none,
  h := fun a₁ a₂, rfl }

#check myFun 3
#check @myFun nat 3            -- works

#check myFun' _ 3
#check myFun' nat 3            -- works

/-
The single, double, and serif uparrows don't really work in Lean 3.

#check ⇑myFun 3
#check ⇑(myFun' _) 3
#check ⇑(myFun' Nat) 3
-/
