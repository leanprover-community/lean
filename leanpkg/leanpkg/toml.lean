/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import data.buffer.parser

-- I'd like to contribute a new naming convention:
-- CamelCase for non-terminals.

def join (sep : string) : list string → string
| [x]     := x
| []      := ""
| (x::xs) := x ++ sep ++ join xs

namespace toml

inductive value : Type
| str : string → value
| nat : ℕ → value
| bool : bool → value
| table : list (string × value) → value

namespace value

private def escapec : char → string
| '\"' := "\\\""
| '\t' := "\\t"
| '\n' := "\\n"
| '\\' := "\\\\"
| c    := string.singleton c

private def escape (s : string) : string :=
s.fold "" (λ s c, s ++ escapec c)

/- TODO(Leo): has_to_string -/
private mutual def repr_core, repr_pairs
with repr_core : value → string
| (value.str s)    := "\"" ++ escape s ++ "\""
| (value.nat n)    := repr n
| (value.bool tt)  := "true"
| (value.bool ff)  := "false"
| (value.table cs) :=
  have @has_well_founded.r _
    (@has_well_founded_of_has_sizeof _ (psum.has_sizeof_alt _ _))
    (psum.inr cs) (psum.inl (table cs)) :=
  begin
    unfold has_well_founded.r sizeof_measure measure inv_image,
    unfold sizeof has_sizeof.sizeof value.sizeof psum.alt.sizeof,
    rw [nat.add_comm],
    exact nat.lt_succ_self _,
  end,
  "{" ++ repr_pairs cs ++ "}"
with repr_pairs : list (string × value) → string
| []               := ""
| [(k, v)]         :=
  have @has_well_founded.r _
    (@has_well_founded_of_has_sizeof _ (psum.has_sizeof_alt _ _))
    (psum.inl v) (psum.inr [(k, v)]) :=
  begin
    apply nat.lt_succ_of_lt,
    unfold sizeof has_sizeof.sizeof prod.sizeof,
    rw [← nat.add_assoc],
    apply nat.lt_add_of_pos_left,
    rw [nat.add_comm],
    exact nat.succ_pos _,
  end,
  k ++ " = " ++ repr_core v
| ((k, v)::kvs)    :=
  have @has_well_founded.r _
    (@has_well_founded_of_has_sizeof _ (psum.has_sizeof_alt _ _))
    (psum.inl v) (psum.inr ((k, v) :: kvs)) :=
  begin
    change v.sizeof < 1 + (1 + k.length + v.sizeof) + kvs.sizeof,
    rw [← nat.add_assoc, nat.add_comm, ← nat.add_assoc],
    apply nat.lt_add_of_pos_left,
    rw [nat.add_comm, nat.add_assoc, nat.add_comm],
    exact nat.succ_pos _,
  end,
  have @has_well_founded.r _
    (@has_well_founded_of_has_sizeof _ (@psum.has_sizeof_alt value _ _ _))
    (psum.inr kvs) (psum.inr ((k, v) :: kvs)) :=
  begin
    apply nat.lt_add_of_pos_left,
    rw [nat.add_comm],
    exact nat.succ_pos _,
  end,
  k ++ " = " ++ repr_core v ++ ", " ++ repr_pairs kvs

protected def repr : ∀ (v : value), string
| (table cs) := join "\n" $ do (h, c) ← cs,
  match c with
  | table ds :=
    ["[" ++ h ++ "]\n" ++
     join "" (do (k, v) ← ds,
       [k ++ " = " ++ repr_core v ++ "\n"])]
  | _ := ["<error> " ++ repr_core c]
  end
| v := repr_core v

/- TODO(Leo): has_to_string -/
instance : has_repr value :=
⟨value.repr⟩

def lookup : value → string → option value
| (value.table cs) k :=
  match cs.filter (λ c : string × value, c.fst = k) with
  | [] := none
  | (k,v) ::_ := some v
  end
| _ _ := none

end value

open parser

def Comment : parser unit :=
ch '#' >> many' (sat (≠ '#')) >> optional (ch '\n') >> eps

def Ws : parser unit :=
decorate_error "<whitespace>" $
many' $ one_of' " \t\x0d\n".to_list <|> Comment

def tok (s : string) := str s >> Ws

def StringChar : parser char :=
sat (λc, c ≠ '\"' ∧ c ≠ '\\' ∧ c.val > 0x1f)
 <|> (do str "\\",
         (str "t" >> return '\t') <|>
         (str "n" >> return '\n') <|>
         (str "\\" >> return '\\') <|>
         (str "\"" >> return '\"'))

def BasicString : parser string :=
str "\"" *> (many_char StringChar) <* str "\"" <* Ws

def String := BasicString

def Nat : parser nat :=
do s ← many_char1 (one_of "0123456789".to_list),
   Ws,
   return s.to_nat

def Boolean : parser bool :=
(tok "true" >> return tt) <|>
(tok "false" >> return ff)

def BareKey : parser string := do
cs ← many_char1 $ sat $ λ c, c.is_alpha ∨ c.is_digit ∨ c = '_' ∨ c = '-',
Ws,
return cs

def Key := BareKey <|> BasicString

section
parameter Val : parser value

def KeyVal : parser (string × value) := do
k ← Key, tok "=", v ← Val,
return (k, v)

def StdTable : parser (string × value) := do
tok "[", n ← Key, tok "]",
cs ← many KeyVal,
return (n, value.table cs)

def Table : parser (string × value) := StdTable

def StrVal : parser value :=
value.str <$> String

def NatVal : parser value :=
value.nat <$> Nat

def BoolVal : parser value :=
value.bool <$> Boolean

def InlineTable : parser value :=
tok "{" *> (value.table <$> sep_by (tok ",") KeyVal) <* tok "}"

end

def Val : parser value :=
fix $ λ Val, StrVal <|> NatVal <|> BoolVal <|> InlineTable Val

def Expression := Table Val

def File : parser value :=
Ws *> (value.table <$> many Expression)

/-
#eval run_string File $
   "[package]\n" ++
   "name = \"sss\"\n" ++
   "version = \"0.1\"\n" ++
   "timeout = 10\n" ++
   "\n" ++
   "[dependencies]\n" ++
   "library_dev = { git = \"https://github.com/leanprover/library_dev\", rev = \"master\" }"
-/

end toml
