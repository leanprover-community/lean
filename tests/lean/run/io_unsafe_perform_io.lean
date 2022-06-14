
import system.io
open list io

def getD {ε α : Type} (d : α): except ε α → α
  | (except.ok a) := a
  | (except.error e) := d

meta def f (i : nat) : nat :=
   getD 100 $ io.unsafe_perform_io (do put_str "value: ", print i, put_str "\n", pure i)

#eval list.map f [0,1,2,3,4]
