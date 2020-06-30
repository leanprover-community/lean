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
#eval (sf.of_eformat <$> tactic.pp_tagged `({w, x, y, z} : set nat)) >>= tactic.trace -- fa, afa, aafa, aaaa
-- example : {x : nat | x = 3} = {4} := begin end

constant bar [inhabited ℕ] [inhabited ℕ] : ℕ → ℤ
#eval (sf.of_eformat <$> tactic.pp_tagged `((int.of_nat = bar))) >>= tactic.trace