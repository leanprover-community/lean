section
parameter (k : ℕ)

mutual def foo, bar
with foo : ℕ → ℕ
| 0 := k
| (n+1) :=
  have _ := n.lt_succ_self,
  bar n
with bar : ℕ → ℕ
| 0 := k+10
| (n+1) :=
  have _ := n.lt_succ_self,
  foo n

def baz : ℕ := foo 3

def foo' (n : ℕ) := k+n
def baz' : ℕ := foo' 3

end
