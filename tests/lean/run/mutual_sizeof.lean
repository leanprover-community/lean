inductive tree : Type
| node : list tree → tree

mutual def g, f, h
with g : list tree → ℕ
| [] := 0
| (x :: xs) := f x + g xs
with f : tree → ℕ
| (tree.node children) := 1 + g children
with h : ℕ → ℕ
| x := x

mutual def f1, f2, f3, f4, f5
with f1 : ℕ → unit | (n+1) := f5 n | _ := ()
with f2 : ℕ → unit | (n+1) := f3 n | _ := ()
with f3 : ℕ → unit | (n+1) := f3 n | _ := ()
with f4 : ℕ → unit | (n+1) := f1 n | _ := ()
with f5 : ℕ → unit | (n+1) := f4 n | _ := ()
