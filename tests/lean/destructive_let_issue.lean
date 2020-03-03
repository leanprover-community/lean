/- Bug documented at https://github.com/leanprover-community/lean/issues/55  -/

-- set_option trace.elaborator_detail true
-- set_option trace.type_context.is_def_eq true
-- set_option trace.type_context.is_def_eq_detail true

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
| 0 := tt
| (k+1) := k = k

example : ℕ → bool
| 0 := let x := tt in tt
| (k+1) := k = k

example : ℕ → bool
| 0 := let _ := tt in tt
| (k+1) := k = k

example : ℕ → bool
| 0 := let _ := tt in tt
| (k+1) := if k = k then tt else ff

example : ℕ → bool
| 0 := let _ := tt in tt
| (k+1) := if h : k = k then tt else ff -- succeeds