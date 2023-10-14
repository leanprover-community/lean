def mod5 (a b : ℕ) : Prop := a % 5 = b % 5

infix ` ≡ `:50 := mod5

@[refl] theorem mod5.refl (a : ℕ) : a ≡ a := @rfl _ _

@[symm] theorem mod5.symm (a b : ℕ) : a ≡ b → b ≡ a := eq.symm

@[trans] theorem mod5.trans (a b c : ℕ) : a ≡ b → b ≡ c → a ≡ c := eq.trans

@[congr]
theorem mod5.add (a b c d : ℕ) (h₁ : a ≡ b) (h₂ : c ≡ d) : a + c ≡ b + d := sorry

@[congr]
theorem mod5.congr (a b c d : ℕ) (h1 : a ≡ c) (h2 : b ≡ d) : (a ≡ b) = (c ≡ d) := sorry

example (a b c d : ℕ) (h : a ≡ b + c) (h' : c + c ≡ 2*c) (h'' : b + c + c ≡ b + (c + c)) :
  a + c ≡ b + 2*c :=
begin
  simp only [h, h', h''],
end
