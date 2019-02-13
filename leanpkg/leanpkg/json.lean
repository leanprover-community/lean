
import data.buffer.parser

universes u v

namespace json

open parser

inductive value
| string : string → value
| bool : bool → value
| nat : ℕ → value
| array : unit → list value → value
| object : unit → list (string × value) → value

instance : inhabited value :=
⟨ value.bool tt ⟩

namespace parser

private def escapec : char → string
| '\"' := "\\\""
| '\t' := "\\t"
| '\n' := "\\n"
| '\\' := "\\\\"
| c    := string.singleton c

private def escape (s : string) : string :=
s.fold "" (λ s c, s ++ escapec c)

protected mutual def repr, repr_pairs, repr_array
with repr : value → string
| (value.string s)    := "\"" ++ escape s ++ "\""
-- | (value.nat n)    := repr n
| (value.nat z)  := _root_.repr z
| (value.bool tt)  := "true"
| (value.bool ff)  := "false"
| (value.object _ cs) := "{" ++ repr_pairs cs ++ "}"
| (value.array _ cs) := "[" ++ repr_array cs ++ "]"
with repr_pairs : list (string × value) → string
| []               := ""
| [(k, v)]         := k ++ " = " ++ repr v
| ((k, v)::kvs)    := k ++ " = " ++ repr v ++ ", " ++ repr_pairs kvs
with repr_array : list value → string
| []               := ""
| [v]         := repr v
| (v::vs)    := repr v ++ ", " ++ repr_array vs

instance : has_repr value :=
⟨ json.parser.repr ⟩

meta instance : has_to_format value :=
⟨ to_fmt ∘ json.parser.repr ⟩


-- protected def repr : ∀ (v : value), string
-- | (table cs) := join "\n" $ do (h, c) ← cs,
--   match c with
--   | table ds :=
--     ["[" ++ h ++ "]\n" ++
--      join "" (do (k, v) ← ds,
--        [k ++ " = " ++ repr_core v ++ "\n"])]
--   | _ := ["<error> " ++ repr_core c]
--   end
-- | v := repr_core v

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

def NatVal : parser value :=
value.nat <$> Nat

def Value : parser value :=
fix $ λ Value,
  (tok "[" *> Ws *> value.array ()  <$> sep_by (tok ",") Value <* tok "]") <|>
  (tok "{" *> Ws *> value.object () <$> sep_by (tok ",") (prod.mk <$> String <* tok ":" <*> Value ) <* tok "}") <|>
  decorate_error "value" (
  (value.bool tt <$ tok "true") <|>
  (value.bool ff <$ tok "false") <|>
  NatVal <|>
  (value.string <$> String) <|>
  (decorate_error "value" $ failure) )

end parser

def parse_json : parser value :=
parser.Ws *> parser.Value

def sum.coe {m} [monad m] [monad_fail m] {α} : sum string α → m α
| (sum.inl s) := monad_fail.fail $ "\n" ++ s
| (sum.inr x) := return x

instance {m} [monad m] [monad_fail m] {α} : has_coe (sum string α) (m α) :=
⟨ sum.coe ⟩

def some_data : string := "
{ \"prerelease\": false,
  \"created_at\": \"2016-10-26T21:36:59Z\",
    \"published_at\": \"2016-10-26T22:47:30Z\"
} "

def some_date2 : string := "
[
  {
    \"url\": \"https://api.github.com/repos/jgm/pandoc/releases/15283811\",
    \"assets_url\": \"https://api.github.com/repos/jgm/pandoc/releases/15283811/assets\",
    \"upload_url\": \"https://uploads.github.com/repos/jgm/pandoc/releases/15283811/assets{?name,label}\",
    \"html_url\": \"https://github.com/jgm/pandoc/releases/tag/2.6\",
    \"id\": 15283811,
    \"node_id\": \"MDc6UmVsZWFzZTE1MjgzODEx\",
    \"tag_name\": \"2.6\" } ] "

def some_data3 : string :=
"[
  {
    \"url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/releases/15499268\",
    \"assets_url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/releases/15499268/assets\",
    \"upload_url\": \"https://uploads.github.com/repos/leanprover-community/mathlib-nightly/releases/15499268/assets{?name,label}\",
    \"html_url\": \"https://github.com/leanprover-community/mathlib-nightly/releases/tag/nightly-2019-02-12\",
    \"id\": 15499268,\n    \"node_id\": \"MDc6UmVsZWFzZTE1NDk5MjY4\",
    \"tag_name\": \"nightly-2019-02-12\",
    \"target_commitish\": \"master\",
    \"name\": \"nightly-2019-02-12\",
    \"draft\": false,
    \"author\": {
      \"login\": \"leanprover-mathlib-bot\",
      \"id\": 47432195,
      \"node_id\": \"MDQ6VXNlcjQ3NDMyMTk1\",
      \"avatar_url\": \"https://avatars2.githubusercontent.com/u/47432195?v=4\",
      \"gravatar_id\": \"\",
      \"url\": \"https://api.github.com/users/leanprover-mathlib-bot\",
      \"html_url\": \"https://github.com/leanprover-mathlib-bot\",
      \"followers_url\": \"https:htly/releases/assets/11039536\",
        \"id\": 11039536,
        \"node_id\": \"MDEyOlJlbGVhc2VBc3NldDExMDM5NTM2\",
        \"name\": \"mathlib-scripts-nightly-2019-02-12.tar.gz\",
        \"label\": \"\",
        \"uploader\": {
          \"login\": \"leanprover-mathlib-bot\",
          \"id\": 47432195,
          \"node_id\": \"MDQ6VXNlcjQ3NDMyMTk1\",
          \"avatar_url\": \"https://avatars2.githubusercontent.com/u/47432195?v=4\",
          \"gravatar_id\": \"\",
          \"url\": \"https://api.github.com/users/leanprover-mathlib-bot\",
          \"html_url\": \"https://github.com/leanprover-mathlib-bot\",
          \"followers_url\": \"https://api.github.com/users/leanprover-mathlib-bot/followers\",
          \"following_url\": \"https://api.github.com/users/leanprover-mathlib-bot/following{/other_user}\",
          \"gists_url\": \"https://api.github.com/users/leanprover-mathlib-bot/gists{/gist_id}\",
          \"starred_url\": \"https://api.github.com/users/leanprover-mathlib-bot/starred{/owner}{/repo}\",
          \"subscriptions_url\": \"https://api.githubrelease\": true } },
    \"created_at\": \"2019-02-09T20:24:54Z\",
    \"published_at\": \"2019-02-11T20:53:26Z\",
    \"assets\": [
      {
        \"url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/releases/assets/11035154\",
        \"id\": 11035154,
        \"node_id\": \"MDEyOlJlbGVhc2VBc3NldDExMDM1MTU0\",
        \"name\": \"mathlib-olean-nightly-2019-02-11.tar.gz\",
        \"label\": \"\",
        \"uploader\": {
          \"login\": \"leanprover-mathlib-bot\",
          \"id\": 47432195,
          \"node_id\": \"MDQ6VXNlcjQ3NDMyMTk1\",
          \"avatar_url\": \"https://avatars2.githubusercontent.com/u/47432195?v=4\",
          \"gravatar_id\": \"\",
          \"url\": \"https://api.github.com/users/leanprover-mathlib-bot\",
          \"html_url\": \"https://github.com/leanprover-mathlib-bot\",
          \"followers_url\": \"https://api.github.com/users/leanprover-mathlib-bot/followers\",
          \"following_url\": \"https://api.github.com/users/leanprover-mathlib-bot/following{/other_user}\",
          \"gists_url\": \"https://api.github.com2019-02-11.tar.gz\" }
      }
    ],
    \"tarball_url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/tarball/nightly-2019-02-11\",
    \"zipball_url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/zipball/nightly-2019-02-11\",
    \"body\": \"Mathlib's .olean files and scripts\"
  }
]"

def some_data3' : string :=
"[
  {
    \"url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/releases/15499268\",
    \"assets_url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/releases/15499268/assets\",
    \"upload_url\": \"https://uploads.github.com/repos/leanprover-community/mathlib-nightly/releases/15499268/assets{?name,label}\",
    \"html_url\": \"https://github.com/leanprover-community/mathlib-nightly/releases/tag/nightly-2019-02-12\",
    \"id\": 15499268,\n    \"node_id\": \"MDc6UmVsZWFzZTE1NDk5MjY4\",
    \"tag_name\": \"nightly-2019-02-12\",
    \"target_commitish\": \"master\",
    \"name\": \"nightly-2019-02-12\",
    \"draft\": false,
    \"author\": {
      \"login\": \"leanprover-mathlib-bot\",
      \"id\": 47432195,
      \"node_id\": \"MDQ6VXNlcjQ3NDMyMTk1\",
      \"avatar_url\": \"https://avatars2.githubusercontent.com/u/47432195?v=4\",
      \"gravatar_id\": \"\",
      \"url\": \"https://api.github.com/users/leanprover-mathlib-bot\",
      \"html_url\": \"https://github.com/leanprover-mathlib-bot\",
      \"followers_url\": \"https:htly/releases/assets/11039536\",
        \"id\": 11039536,
        \"node_id\": \"MDEyOlJlbGVhc2VBc3NldDExMDM5NTM2\",
        \"name\": \"mathlib-scripts-nightly-2019-02-12.tar.gz\",
        \"label\": \"\",
        \"uploader\": {
          \"gists_url\": \"https://api.github.com/users/leanprover-mathlib-bot/gists{/gist_id}\",
          \"starred_url\": \"https://api.github.com/users/leanprover-mathlib-bot/starred{/owner}{/repo}\",
          \"subscriptions_url\": \"https://api.githubrelease\" } },
    \"created_at\": \"2019-02-09T20:24:54Z\",
    \"published_at\": \"2019-02-11T20:53:26Z\",
    \"tarball_url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/tarball/nightly-2019-02-11\",
    \"zipball_url\": \"https://api.github.com/repos/leanprover-community/mathlib-nightly/zipball/nightly-2019-02-11\",
    \"body\": \"Mathlib's .olean files and scripts\"
  }
]"

run_cmd do
tactic.trace "",
x ← (↑(run_string parse_json some_data3') : tactic value),
tactic.trace $ x

def fish {m} [monad m] {α β γ} (f : α → m β) (g : β → m γ) (x : α) : m γ :=
f x >>= g

#print notation >>=

infix >=>:55 := fish

variables {m : Type → Type v} [alternative m]

def List : value → m (list value)
| (value.array _ xs) := pure xs
| _ := failure

def Object : value → m (list (string × value))
| (value.object _ xs) := pure xs
| _ := failure

def String : value → m string
| (value.string s) := pure s
| _ := failure

def Nat : value → m ℕ
| (value.nat n) := pure n
| _ := failure

def Bool : value → m bool
| (value.bool b) := pure b
| _ := failure

def Lookup (k : string) : list (string × value) → m value
| [] := failure
| ((k',x) :: xs) :=
 if k = k' then pure x
 else Lookup xs

def Find (f : value → m unit) : list value → m value
| [] := failure
| (x :: xs) :=
x <$ f x <|> Find xs

end json
