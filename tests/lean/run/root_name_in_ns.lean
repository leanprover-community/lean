structure foo := (y : ℕ)

namespace foo

instance _root_.string.has_add : has_add string := ⟨(++)⟩

def _root_.string.frob (x : string) := x ++ x

def frob := "5".frob

meta mutual def _root_.string.meow, woof
with _root_.string.meow : string → ℕ
| s := if s.length = 0 then 0 else woof ⟨s.length⟩
with woof : foo → ℕ
| ⟨0⟩ := 0
| ⟨1⟩ := 0
| ⟨y⟩ := _root_.string.meow y.repr

inductive _root_.string.beautiful : string → Prop
| empty : _root_.string.beautiful ""

structure _root_.string.elsewhere := (x : ℕ)

mutual inductive _root_.a, _root_.b
with _root_.a : Type
| x : ℕ → _root_.a
| y : _root_.b → _root_.a
with _root_.b : Type
| z : _root_.a → _root_.b

end foo

#check string.has_add

#print string.beautiful
#check string.beautiful.empty

#print string.elsewhere
#check string.elsewhere
#check string.elsewhere.mk
#check string.elsewhere.x

#eval "2".meow

#check a
#check a.x
#check a.y
#check b
#check b.z