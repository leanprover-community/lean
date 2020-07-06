open lean (parser)
open lean.parser
open interactive
open tactic

reserve prefix `unquote! `:100
reserve prefix `unquote2! `:100
@[user_notation]
meta def unquote_macro (_ : parse $ tk "unquote!") (e : parse lean.parser.pexpr) : parser pexpr :=
↑(to_expr e >>= eval_expr pexpr)

#eval unquote! ``(1 + 1)

@[user_notation]
meta def unquote_macro' (_ : parse $ tk "unquote2!") (e : parse $ lean.parser.pexpr std.prec.max tt) : parser pexpr :=
-- ↑(to_expr e >>= eval_expr pexpr)
pure ``(1 : ℕ)

#eval unquote2! (x + 1) -- this shouldn't cause an error because the expression is parsed
                        -- as a pattern

reserve infix ` +⋯+ `:65
@[user_notation]
meta def upto_notation (e₁ : parse lean.parser.pexpr) (_ : parse $ tk "+⋯+") (n₂ : ℕ) : parser pexpr :=
do n₁ ← ↑(to_expr e₁ >>= eval_expr nat),
   pure $ (n₂+1∸n₁).repeat (λ i e, ``(%%e + %%(reflect $ n₁ + i))) ``(0)

#check 1 +⋯+ 10

@[user_notation]
meta def no_tk (e₁ : parse lean.parser.pexpr) := e₁

@[user_notation]
meta def no_parser (e₁ : parse $ tk "(") := e₁
