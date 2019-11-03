/- Bug documented at https://github.com/leanprover-community/lean/issues/55  -/

example : bool :=
  let x : false → Prop := λ x, match x with end in
  let x : bool := match 4 with
  | j := @to_bool (j = j) _
  end in tt

example : bool :=
  let x := match 0 with y := ff end in
  match 0 with
  | k := k = k
  end

example : ℕ → bool
| 0 := let _ := 3 in tt
| (k+1) := k = k
