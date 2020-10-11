example {α β} (a : α) (b : β) : unit :=
begin
  rename a a',              -- rename-compatible syntax
  guard_hyp a' : α,

  rename a' → a,            -- more suggestive syntax
  guard_hyp a : α,

  rename [a a', b b'],      -- parallel renaming
  guard_hyp a' : α,
  guard_hyp b' : β,

  rename [a' → a, b' → b],  -- ditto with alternative syntax
  guard_hyp a : α,
  guard_hyp b : β,

  rename [a → b, b → a],    -- renaming really is parallel
  guard_hyp a : β,
  guard_hyp b : α,

  rename b a,               -- shadowing is allowed (but guard_hyp doesn't like it)

  rename d e,               -- cannot rename nonexistent hypothesis
  exact ()
end


example {α} [decidable α] (a : α) : unit :=
begin
  rename a a', -- renaming works after frozen local instances

  rename α α', -- renaming doesn't work before frozen local instances
end
