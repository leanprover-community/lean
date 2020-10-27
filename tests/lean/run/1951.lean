instance my_pow : has_pow ℕ ℕ :=
⟨λ x n, nat.rec_on n 1 (λ _ ih, ih * x)⟩

#eval 2 ^ (3 ^ 2)
#eval 2 ^ 3 ^ 2

example (a b c : nat) : a ^ (b ^ c) = a ^ b ^ c :=
rfl
