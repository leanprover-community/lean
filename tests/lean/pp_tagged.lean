
namespace widget.interactive_expression
meta def sf.repr : sf → format
| (sf.tag_expr addr e a) := format.group $ format.nest 2 $
  "(tag_expr " ++ to_fmt addr ++ format.line ++
    "`(" ++ to_fmt e ++ ")" ++ format.line ++ a.repr ++ ")"
| (sf.compose a b) := a.repr ++ format.line ++ b.repr
| (sf.of_string s) := repr s

meta instance : has_to_format sf := ⟨sf.repr⟩
meta instance : has_to_string sf := ⟨λ s, s.repr.to_string⟩
meta instance : has_repr sf := ⟨λ s, s.repr.to_string⟩
end widget.interactive_expression

open widget.interactive_expression

constant f : nat → nat → nat → nat
constants w x y z : nat

#eval (sf.of_eformat <$> tactic.pp_tagged `(f x y z)) >>= tactic.trace

#eval (sf.of_eformat <$> tactic.pp_tagged `(x + y + z)) >>= tactic.trace

#eval (sf.of_eformat <$> tactic.pp_tagged `(x = y)) >>= tactic.trace

#eval (sf.of_eformat <$> tactic.pp_tagged `((int.of_nat = coe))) >>= tactic.trace

#eval (sf.of_eformat <$> tactic.pp_tagged `((x,y))) >>= tactic.trace -- fa, a

#eval (sf.of_eformat <$> tactic.pp_tagged `((w,x,y,z))) >>= tactic.trace -- fa, afa, aafa, aaa
#eval (sf.of_eformat <$> tactic.pp_tagged `({x : nat | false})) >>= tactic.trace -- at, ab
-- insert w (insert x (insert y (singleton z)))
#eval (sf.of_eformat <$> tactic.pp_tagged `({w, x, y, z} : set nat) >>= tactic.trace -- fa, afa, aafa, aaaa
-- example : {x : nat | x = 3} = {4} := begin end

