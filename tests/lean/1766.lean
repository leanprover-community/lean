inductive is_some (x : option nat) : Prop
  | mk : ∀ value : nat, x = some value → is_some

def value_1 (x : option nat) (H : is_some x)
   : nat :=
begin
   destruct x; intros,
   {destruct H, -- ERROR: `is_some` can only eliminate into Prop
    intros, clear _x_2, rw _x at _x_1, contradiction},
   {assumption}
end

def value_2 (x : option nat) (H : is_some x)
   : x = x :=
begin
   destruct x; intros,
   {destruct H,
    intros, rw a at _x},
   {refl}
end

inductive is_some' (x : option nat) : Type
  | mk : ∀ value : nat, x = some value → is_some'

def value_3 (x : option nat) (H : is_some' x)
   : nat :=
begin
   destruct x; intros,
   {destruct H,
    intros, clear a_1, rw a at _x, contradiction},
   {assumption}
end
