def stack := list nat
instance : has_concat stack :=
by unfold stack; apply_instance

example (s : stack) : s ++ [] = s :=
begin
  induction s,
  refl, apply list.concat_nil
end
