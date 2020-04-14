open tactic expr

run_cmd do
  n ← mk_local_def  `n `(bool → bool),
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations [] [a,b] n
    (sum.inr
         [ ([``(tt)], ``(ff)),
           ([``(ff)], ``(tt))  ])
         ff

#print n._main
#print prefix n

run_cmd do
  m ← mk_local_def  `m `(bool → bool),
  add_defn_equations [] [] m
         (sum.inr [ ([``(tt)], ``(ff)),
                    ([``(ff)], ``(tt))  ])
         tt

#print m
#print prefix m

#eval m tt
run_cmd do
  m ← mk_local_def  `mm `(bool → bool),
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations [] [a,b] m
     (sum.inr [ ([``(tt)], to_pexpr $ m `(ff)),
                ([``(ff)], to_pexpr $ m `(tt))  ])
     ff

#print mm

run_cmd do
  mm ← mk_local_def  `mm `(bool → bool),
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  add_defn_equations [] [a,b] mm
    (sum.inr [  ])
    ff

#print mm._main

run_cmd do
  plus ← mk_local_def  `plus' `(nat → nat),
  x ← mk_local_def `x `(nat),
  a ← mk_local_def `a `(nat),
  b ← mk_local_def `b `(nat),
  add_defn_equations [] [a,b] plus
    (sum.inr [ ([ ``(nat.zero) ], to_pexpr b),
               ([ ``(nat.succ %%x) ], to_pexpr $ plus x) ]) ff

#print plus'

#print prefix plus'

open level

run_cmd do
  let u := param `u,
  α ← mk_local' `α binder_info.implicit (sort (succ u)),
  let list_t := @const tt ``list [u] α,
  append ← mk_local_def  `foo_append $ imp list_t list_t,
  xs ← mk_local_def `xs list_t,
  y ← mk_local_def `y α,
  ys ← mk_local_def `ys list_t,
  let list_cons := @const tt ``list.cons [u],
  add_defn_equations [`u] [α,xs] append
    (sum.inr [ ([ ``(@list.nil %%α) ], to_pexpr xs),
               ([ ``(%%y :: %%ys) ], to_pexpr $ list_cons α y $ append ys) ]) ff

#print foo_append._main

#print prefix foo_append
universes u

inductive vec (α : Type u) : ℕ → Type u
| nil {} : vec 0
| cons {n : ℕ} : α → vec n → vec n.succ

run_cmd do
  let u := param `u,
  let v := param `v,
  α ← mk_local' `α binder_info.implicit (sort (succ u)),
  β ← mk_local' `β binder_info.implicit (sort (succ v)),
  f ← mk_local_def `f $ α.imp β,
  n ← mk_local' `n binder_info.default `(nat),
  let vec_t := @const tt ``vec [u] α n,
  let vec_t' := @const tt ``vec [v] β n,
  map ← mk_local_def  `vec.map $ pis [n] $ imp vec_t vec_t',
  y ← mk_local_def `y α,
  ys ← mk_local_def `ys vec_t,
  let vec_nil := @const tt ``vec.nil [v],
  let vec_cons := @const tt ``vec.cons [v],
  add_defn_equations [`u,`v] [α,β,f] map
    (sum.inr
      [ ([ ``(._), ``(@vec.nil %%α) ], to_pexpr $ vec_nil β),
        ([ ``(.(nat.succ %%n)), ``(@vec.cons %%α %%n %%y %%ys) ], to_pexpr $ vec_cons β n (f y) $ map n ys ) ] )
    ff

#print vec.map._main
#print prefix vec.map

run_cmd do
  let u := param `u,
  let v := param `v,
  α ← mk_local' `α binder_info.implicit (sort (succ u)),
  β ← mk_local' `β binder_info.implicit (sort (succ v)),
  f ← mk_local_def `f $ α.imp β,
  n ← mk_local' `n binder_info.implicit `(nat),
  let vec_t := @const tt ``vec [u] α n,
  let vec_t' := @const tt ``vec [v] β n,
  map ← mk_local_def  `vec.map' $ pis [n] $ imp vec_t vec_t',
  y ← mk_local_def `y α,
  ys ← mk_local_def `ys vec_t,
  let vec_nil := @const tt ``vec.nil [v],
  let vec_cons := @const tt ``vec.cons [v],
  add_defn_equations [`u,`v] [α,β,f] map
    (sum.inr [ ([ ``(._), ``(@vec.nil %%α) ], to_pexpr $ vec_nil β),
               ([ ``(.(nat.succ %%n)), ``(@vec.cons %%α %%n %%y %%ys) ], to_pexpr $ vec_cons β n (f y) $ map n ys ) ])
    ff

#check vec.map'._main
#print vec.map'._main
#print prefix vec.map'
#print vec.map'._main._meta_aux

run_cmd do
  n ← mk_local_def `n₂ `(bool),
  b ← mk_local_def `b `(bool),
  a ← mk_local_def `a `(bool),
  e ← mk_app ``band [a,b],
  add_defn_equations [] [a,b] n
    (sum.inl $ to_pexpr e)
         ff

#print n₂
#print prefix n₂
