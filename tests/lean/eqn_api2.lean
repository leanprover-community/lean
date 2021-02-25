
mutual def f, g
with f : list ℕ -> ℕ
| [] := 0
| (x :: xs) := x + g xs
with g : list ℕ -> ℕ
| [] := 0
| (x :: xs) := f xs

def foo (a : Type) (x : a) : option a -> a
| none := x
| (some y) := y
