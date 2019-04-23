open tactic expr

run_cmd do
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations `n [a,b] `(bool → bool)
  (λ fn, [ ([`(tt)], `(ff)),
           ([`(ff)], `(tt))  ])
  ff

#print n._main
#print prefix n

run_cmd do
  add_defn_equations `m [] `(bool → bool)
  (λ fn, [ ([`(tt)], `(ff)),
           ([`(ff)], `(tt))  ])
  tt

#print m
#print prefix m

#eval m tt

run_cmd do
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations `m [a,b] `(bool → bool)
  (λ fn, [ ([`(tt)], fn `(ff)),
           ([`(ff)], fn `(tt))  ])
  ff

run_cmd do
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations `mm [a,b] `(bool → bool)
  (λ fn, [  ])
  ff

#print mm._main

run_cmd do
  x ← mk_local_def `x `(nat),
  a ← mk_local_def `a `(nat),
  b ← mk_local_def `b `(nat),
  add_defn_equations `plus' [a,b] `(nat → nat) (λ fn,
    [ ([ `(nat.zero) ], b),
      ([ (`(nat.succ) : expr) x ], fn x) ]) ff

#print plus'

#print prefix plus'
