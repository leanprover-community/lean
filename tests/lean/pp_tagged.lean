open widget.interactive_expression

constant f : nat → nat → nat → nat
constants w x y z : nat

#eval (sf.of_eformat <$> tactic.pp_tagged `(f x y z)) >>= tactic.trace

#eval (sf.of_eformat <$> tactic.pp_tagged `(x + y + z)) >>= tactic.trace

#eval (sf.of_eformat <$> tactic.pp_tagged `(x = y)) >>= tactic.trace

#eval (sf.of_eformat <$> tactic.pp_tagged `((x,y))) >>= tactic.trace -- fa, a

#eval (sf.of_eformat <$> tactic.pp_tagged `((w,x,y,z))) >>= tactic.trace -- fa, afa, aafa, aaa
#eval (sf.of_eformat <$> tactic.pp_tagged `({x : nat | false})) >>= tactic.trace -- at, ab

#eval (sf.of_eformat <$> tactic.pp_tagged `({w, x, y, z} : set nat)) >>= tactic.trace -- fa, afa, aafa, aaaa

#eval (sf.of_eformat <$> tactic.pp_tagged `((int.of_nat = coe))) >>= tactic.trace
constant bar [inhabited ℕ] [inhabited ℕ] : ℕ → ℤ
constant foo (α : Type) [inhabited ℕ] [inhabited ℕ] : ℕ → ℤ
#eval (sf.of_eformat <$> tactic.pp_tagged `((int.of_nat = bar))) >>= tactic.trace
#eval (sf.of_eformat <$> tactic.pp_tagged `((int.of_nat = (foo nat)))) >>= tactic.trace
