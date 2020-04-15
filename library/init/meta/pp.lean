prelude
import init.meta.expr_address init.meta.local_context init.meta.tactic

/-- An alternative to format that keeps structural information about the expression. -/
meta inductive magic
| tag_expr : expr.address → expr → magic → magic
| compose : magic → magic → magic
| group : magic → magic
| nest : nat → magic → magic
| highlight : format.color → magic → magic
| format : format → magic
-- | tag_name : name → format → magic
open format
meta def magic.to_fmt : magic → format
| (magic.compose m1 m2) := format.compose (magic.to_fmt m1) (magic.to_fmt m2)
| (magic.group m1) := format.group (magic.to_fmt m1)
| (magic.nest i m) := format.nest i $ magic.to_fmt m
| (magic.highlight c m) := format.highlight (magic.to_fmt m) c
| (magic.format f) := f
| (magic.tag_expr ea e m) :=
  "[" ++ (string.join $ list.map nat.has_to_string.to_string $ list.map expr.coord.code $ list.reverse ea) ++ "]" ++ group(nest 1 $ "{" ++ line ++ magic.to_fmt m ++ "}")

meta instance magic.has_to_fmt : has_to_format magic := ⟨magic.to_fmt⟩
meta instance magic.repr : has_repr magic := ⟨format.to_string ∘ magic.to_fmt⟩

meta constant tactic_state.pp_magic   : tactic_state → expr → magic
-- set_option pp.all true

-- def trisum : ℕ → ℕ → ℕ → Prop
-- | a b c := a + b + c = 4

-- notation `[` a `#` b `#` c `]` := trisum a b c

-- example {P Q R: Prop} {J : Prop → Prop → Prop → Prop} : [4#5#6] = [4#5#6] :=
-- begin
--    (do
--       x ← tactic.read,
--       t ← tactic.target,
--       m ← pure $ tactic_state.pp_magic x t,
--       tactic.trace m,
--       pure ()
--    ),
--    intros,
--    refl
-- end



