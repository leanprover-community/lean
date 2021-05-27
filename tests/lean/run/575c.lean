def modeq (n a b : ℕ) := a % n = b % n

notation a ` ≡ `:50 b ` [MOD `:50 n `]`:0 := modeq n a b

@[symm] protected theorem modeq.symm {a b n} :
  a ≡ b [MOD n] → b ≡ a [MOD n] :=
eq.symm

example (a b m n : ℕ) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD m] :=
by cc
