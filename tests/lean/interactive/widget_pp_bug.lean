example : ((1 : ℕ) : ℤ) = (fun x : ℤ, x + 3) 2 :=
by skip


def f : ℕ → ℕ → ℕ → ℕ
| x y z := z + y * x

example : f 1 2 3 = if 1 < 2 then f 3 2 1 else 3 :=
by skip

-- [todo] write input tests that the correct addresses are emitted