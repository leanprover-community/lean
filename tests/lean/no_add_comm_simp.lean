universe u

run_cmd tactic.has_attribute `simp `mul_assoc
run_cmd tactic.has_attribute `simp `add_assoc

run_cmd tactic.has_attribute `simp `mul_comm >>= tactic.is_fail
run_cmd tactic.has_attribute `simp `add_comm

run_cmd tactic.has_attribute `simp `add_left_comm
run_cmd tactic.has_attribute `simp `mul_left_comm