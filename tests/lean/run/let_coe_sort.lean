inductive foo | bar

instance : has_coe_to_sort foo :=
⟨Type, λ _, unit⟩

set_option pp.all true

example : true :=
begin
  let x : foo.bar := (),
  have y : foo.bar := (),
  suffices z : foo.bar,
  trivial,
  exact (),
end

example : true :=
let x : foo.bar := () in
have y : foo.bar, from (),
trivial

example : foo.bar → true :=
begin
  assume x : foo.bar,
  trivial
end
