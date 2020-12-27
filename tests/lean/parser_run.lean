open lean.parser

meta def parse_hello : tactic unit := do
  e ← lean.parser.run (lean.parser.get_env) "hello",
  e2 ← tactic.get_env,
  tactic.trace (to_bool $ e.fingerprint = e2.fingerprint),
  n ← lean.parser.run (lean.parser.ident) "hello",
  tactic.trace n.to_string

run_cmd parse_hello