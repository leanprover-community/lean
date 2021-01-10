inductive statement : Type
| Sswitch   : list (option ℤ × statement) → statement
open statement

mutual def find_label, find_label_ls
with find_label : statement → nat → option (statement × nat)
| (Sswitch sl)  :=
  have @has_well_founded.r _
    (@has_well_founded_of_has_sizeof _ (psum.has_sizeof_alt _ _))
    (psum.inr sl) (psum.inl (Sswitch sl)) :=
  begin
    unfold has_well_founded.r sizeof_measure measure inv_image,
    unfold sizeof has_sizeof.sizeof psum.alt.sizeof statement.sizeof,
    rw [nat.add_comm],
    exact nat.lt_succ_self _,
  end,
  λ k, find_label_ls sl k
with find_label_ls : list (option ℤ × statement) → nat → option (statement × nat)
| []       := λk, none
| ((_, s) :: sl') :=
  have @has_well_founded.r _
    (@has_well_founded_of_has_sizeof _ (psum.has_sizeof_alt _ _))
    (psum.inl s) (psum.inr ((_x, s) :: sl')) :=
  begin
    unfold has_well_founded.r sizeof_measure measure inv_image,
    unfold sizeof has_sizeof.sizeof psum.alt.sizeof list.sizeof prod.sizeof,
    rw [nat.add_comm, ← nat.add_assoc, ← nat.add_assoc],
    apply nat.lt_add_of_pos_left,
    rw [nat.add_comm, ← nat.add_assoc],
    exact nat.succ_pos _,
  end,
  have @has_well_founded.r _
    (@has_well_founded_of_has_sizeof _ (psum.has_sizeof_alt _ _))
    (psum.inr sl') (@psum.inr statement _ ((_x, s) :: sl')) :=
  begin
    unfold has_well_founded.r sizeof_measure measure inv_image,
    unfold sizeof has_sizeof.sizeof psum.alt.sizeof list.sizeof prod.sizeof,
    rw [nat.add_comm],
    apply nat.lt_add_of_pos_right,
    rw [nat.add_comm],
    exact nat.succ_pos _,
  end,
  λk, find_label s k <|> find_label_ls sl' k

example : find_label_ls [] = λ k, none :=
by simp [find_label_ls]

example (n s sl) : find_label_ls ((n, s)::sl) = λ k, find_label s k <|> find_label_ls sl k :=
by simp [find_label_ls]
