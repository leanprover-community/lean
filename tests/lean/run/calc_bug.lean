definition foo (a : Type) :=
calc a = a : rfl

example (eq : ℕ) : 1 = 1 :=
by calc 1 = 1 : rfl
      ... = 1 : rfl

example (a : Prop) (implies : ℕ) : a → a :=
by calc a → a : id
      ... → a : id
