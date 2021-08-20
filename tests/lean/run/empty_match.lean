open nat

definition not_false' (a : nat) : ¬ false :=
assume H : false,
match H with
end

#check _root_.not_false'
