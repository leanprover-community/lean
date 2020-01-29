open tactic

#eval
([`(ℕ), `(1 + 0)] : list expr).mmap' $ λ e : expr, do
trace (e, e.get_weight, e.get_depth)
