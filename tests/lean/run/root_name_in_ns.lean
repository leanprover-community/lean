namespace foo

instance _root_.string.has_add : has_add string := ⟨(++)⟩

def _root_.string.frob (x : string) := x ++ x

def frob := "5".frob

inductive _root_.string.beautiful : string → Prop
| empty : _root_.string.beautiful ""

structure _root_.string.elsewhere := (x : ℕ)

end foo

#check string.has_add

#print string.beautiful
#check string.beautiful.empty

#print string.elsewhere
#check string.elsewhere
#check string.elsewhere.mk
#check string.elsewhere.x
