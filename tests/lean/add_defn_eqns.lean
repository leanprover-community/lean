open tactic expr

run_cmd do
  n ← mk_local_def  `n `(bool → bool),
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations [] [a,b] n
         [ ([`(tt)], `(ff)),
           ([`(ff)], `(tt))  ]
         ff

#print n._main
#print prefix n

run_cmd do
  m ← mk_local_def  `m `(bool → bool),
  add_defn_equations [] [] m
         [ ([`(tt)], `(ff)),
           ([`(ff)], `(tt))  ]
         tt

#print m
#print prefix m

#eval m tt

run_cmd do
  m ← mk_local_def  `m `(bool → bool),
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations [] [a,b] m
     [ ([`(tt)], m `(ff)),
       ([`(ff)], m `(tt))  ]
     ff

run_cmd do
  mm ← mk_local_def  `mm `(bool → bool),
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations [] [a,b] mm
    [  ]
    ff

#print mm._main

run_cmd do
  plus ← mk_local_def  `plus' `(nat → nat),
  x ← mk_local_def `x `(nat),
  a ← mk_local_def `a `(nat),
  b ← mk_local_def `b `(nat),
  add_defn_equations [] [a,b] plus
    [ ([ `(nat.zero) ], b),
      ([ (`(nat.succ) : expr) x ], plus x) ] ff

#print plus'

#print prefix plus'

open level

run_cmd do
  α ← mk_local' `α binder_info.implicit (sort (succ zero)),
  let list_t := @const tt ``list [zero] α,
  append ← mk_local_def  `foo_append $ imp list_t list_t,
  xs ← mk_local_def `xs list_t,
  y ← mk_local_def `y α,
  ys ← mk_local_def `ys list_t,
  let list_nil := @const tt ``list.nil [zero],   -- notice: we are not applying `nil` and `cons` to `α`
  let list_cons := @const tt ``list.cons [zero], -- because `α` is not a variable bound by those constructors
  add_defn_equations [`u] [α,xs] append
    [ ([ list_nil ], xs),
      ([ list_cons y ys ], list_cons α y $ append ys) ] ff
    -- in `list_cons y $ append ys`, we do not apply `α` presumably
    -- because we are dealing with a preterm

#print foo_append._main

#print prefix foo_append
