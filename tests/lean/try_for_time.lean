run_cmd do {
  (tactic.try_for_time 1000 (tactic.sleep 5000 *> tactic.sleep 5000 *> tactic.trace "NOT OKAY")) <|> tactic.trace "OKAY"
}

run_cmd do {
  tactic.try_for_time 1000 (tactic.try_for 1000 (tactic.sleep 3000 *> tactic.trace "NOT OKAY")) <|> tactic.trace "OKAY"
}

run_cmd do {
  (tactic.try_for_time 10000 $ tactic.try_for 1 $
  tactic.using_new_ref (0 : ℕ) $
    λ r, tactic.iterate_at_most' 500000
      (do val ← tactic.read_ref r,
          tactic.write_ref r (val + 1),
          (guard (val < 300) <|> tactic.trace format! "GUARD FAILED, VALUE IS {val}"))) <|> tactic.trace "OKAY"
}
