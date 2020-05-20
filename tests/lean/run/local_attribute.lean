
local attribute [instance, priority 0] classical.prop_decidable

open tactic

run_cmd do
  (p,_) ← has_attribute `instance ``nat.has_add,
  guard p,
  (p,_) ← has_attribute `instance ``classical.prop_decidable,
  guard (¬ p),
  skip
