example (n : ℕ) (h : n + n ≠ 0) : n ≠ 0 :=
by refine mt (λ hz, _) h; rw hz
