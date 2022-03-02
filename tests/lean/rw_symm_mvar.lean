theorem nat.mul_div_left' (n : ℕ) {m : ℕ} (H : 0 < m) : n = n * m / m :=
by rwa nat.mul_div_left

example (x y : ℕ) (h : 0 < x) (h1 : y = 1) : y * x / x = 1:=
begin
  rwa ← nat.mul_div_left' _ h,
end
