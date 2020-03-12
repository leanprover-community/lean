
meta def tactic.interactive.test (a : interactive.parse
  (lean.parser.of_tactic (@tactic.fail ℕ _ _ "oh no"))) :=
tactic.skip

example : true := begin test end -- should be "oh no"
