/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/
import leanpkg.manifest system.io leanpkg.proc leanpkg.git leanpkg.json

namespace leanpkg

def assignment := list (string × string)

namespace assignment
def empty : assignment := []

def find : assignment → string → option string
| []              s := none
| ((k, v) :: kvs) s :=
  if k = s then some v else find kvs s

def contains (a : assignment) (s : string) : bool :=
(a.find s).is_some

def insert (a : assignment) (k v : string) : assignment :=
if a.contains k then a else (k, v) :: a

def fold {α} (i : α) (f : α → string → string → α) : assignment → α :=
list.foldl (λ a ⟨k, v⟩, f a k v) i

end assignment

@[reducible] def solver := state_t assignment io
instance {α : Type} : has_coe (io α) (solver α) := ⟨state_t.lift⟩

def not_yet_assigned (d : string) : solver bool := do
assg ← get,
return $ ¬ assg.contains d

def resolved_path (d : string) : solver string := do
assg ← get,
some path ← return (assg.find d) | io.fail "",
return path

-- TODO(gabriel): directory existence testing
def dir_exists (d : string) : io bool := do
ch ← io.proc.spawn { cmd := "test", args := ["-d", d] },
ev ← io.proc.wait ch,
return $ ev = 0

-- TODO(gabriel): windows?
def resolve_dir (abs_or_rel : string) (base : string) : string :=
if abs_or_rel.front = '/' then
  abs_or_rel -- absolute
else
  base ++ "/" ++ abs_or_rel

-- GET /repos/:owner/:repo/releases

def run_cm (cmd : io.process.spawn_args) : io string := do
h ← io.proc.spawn { stdout := io.process.stdio.piped, .. cmd },
io.iterate "" $ λ out,
do { done ← io.fs.is_eof h.stdout,
    if done
    then return none
    else do
     xs ← buffer.to_string <$> io.fs.get_line h.stdout,
     return $ some $ out ++ xs } <*
io.proc.wait h


def binary_archive_url (nightly : nightly_store) (commit : string) : io (string × string) := do
tok ← io.cmd { cmd := "git", args := ["config","--get","github.oauthtoken"] },
let tok := (tok.to_list.filter (λ c : char, ¬ c.is_whitespace)).as_string,
let url := "https://" ++ tok ++ "@api.github.com/repos/" ++ nightly.user ++ "/" ++ nightly.repo,
tags ← run_cm { cmd := "curl", args := ["-s",url ++ "/tags"] },
tags ← (parser.run_string json.parse_json tags : io json.value),
releases ← run_cm { cmd := "curl", args := ["-s",url ++ "/releases"] },
releases ← (parser.run_string json.parse_json releases : io json.value),
tags ← json.List tags,
t ← json.Find (json.Object >=> json.Lookup "commit" >=> json.Object >=> json.Lookup "sha" >=> json.String >=> λ s, guard $ s = commit) tags >>= json.Object >>= json.Lookup "name" >>= json.String,
rel ← json.List releases >>= json.Find (json.Object >=> json.Lookup "tag_name" >=> json.String >=> λ s, guard $ s = t)
  >>= json.Object >>= json.Lookup "assets" >>= json.List
  >>= json.Find (json.Object >=> json.Lookup "name" >=> json.String >=> λ s, guard $ nightly.ar_prefix.to_list.is_prefix_of s.to_list)
  >>= json.Object,
io.print_ln $ rel.map prod.fst,
name ← json.Lookup "name" rel >>= json.String,
url ← json.Lookup "browser_download_url" rel >>= json.String,
pure $ prod.mk name $ url -- ++ "/" ++ name

def insert_token (url tok : string) : string :=
"https://" ++ tok ++ "@" ++ list.as_string (url.to_list.drop  "https://".length)

def download_archive (n url : string) : io unit := do
tok ← io.cmd { cmd := "git", args := ["config","--get","github.oauthtoken"] },
let tok := (tok.to_list.filter (λ c : char, ¬ c.is_whitespace)).as_string,
h ← io.proc.spawn { cmd := "wget", args := ["-O",n,"-q","--auth-no-challenge","--header='Accept:application/octet-stream'",insert_token url tok ] },
io.proc.wait h, pure ()

def expand_archive (n dest : string) : io unit := do
run_cm { cmd := "tar", args := ["-C",dest,"-zxvf",n] } >>= io.print_ln

def fetch_olean (m : manifest) (commit out_path : string) : io unit :=
do { some store ← pure m.nightly,
     (n,url) ← binary_archive_url  store commit,
     download_archive n url,
     expand_archive n out_path } <|> pure ()

def materialize (relpath : string) (dep : dependency) : solver punit :=
match dep.src with
| (source.path dir) := do
  let depdir := resolve_dir dir relpath,
  io.put_str_ln $ dep.name ++ ": using local path " ++ depdir,
  modify $ λ assg, assg.insert dep.name depdir
| (source.git url rev branch) := do
  let depdir := "_target/deps/" ++ dep.name,
  already_there ← dir_exists depdir,
  if already_there then do {
    io.put_str $ dep.name ++ ": trying to update " ++ depdir ++ " to revision " ++ rev,
    io.put_str_ln $ match branch with | none := "" | some branch := "@" ++ branch end,
    hash ← git_parse_origin_revision depdir rev,
    rev_ex ← git_revision_exists depdir hash,
    when (¬rev_ex) $
      exec_cmd {cmd := "git", args := ["fetch"], cwd := depdir}
  } else do {
    io.put_str_ln $ dep.name ++ ": cloning " ++ url ++ " to " ++ depdir,
    exec_cmd {cmd := "mkdir", args := ["-p", depdir]},
    exec_cmd {cmd := "git", args := ["clone", url, depdir]}
  },
  hash ← git_parse_origin_revision depdir rev,
  exec_cmd {cmd := "git", args := ["checkout", "--detach", hash], cwd := depdir},
  d' ← manifest.from_file $ depdir ++ "/" ++ "leanpkg.toml",
  fetch_olean d' hash depdir,
  modify $ λ assg, assg.insert dep.name depdir
end

def solve_deps_core : ∀ (rel_path : string) (d : manifest) (max_depth : ℕ), solver unit
| _ _ 0 := io.fail "maximum dependency resolution depth reached"
| relpath d (max_depth + 1) := do
deps ← monad.filter (not_yet_assigned ∘ dependency.name) d.dependencies,
deps.mmap' (materialize relpath),
deps.mmap' $ λ dep, do
  p ← resolved_path dep.name,
  d' ← manifest.from_file $ p ++ "/" ++ "leanpkg.toml",
  when (d'.name ≠ dep.name) $
    io.fail $ d.name ++ " (in " ++ relpath ++ ") depends on " ++ d'.name ++
      ", but resolved dependency has name " ++ dep.name ++ " (in " ++ p ++ ")",
  solve_deps_core p d' max_depth

def solve_deps (d : manifest) : io assignment := do
(_, assg) ← (solve_deps_core "." d 1024).run $ assignment.empty.insert d.name ".",
return assg

def construct_path_core (depname : string) (dirname : string) : io (list string) :=
list.map (λ relpath, dirname ++ "/" ++ relpath) <$>
manifest.effective_path <$> (manifest.from_file $ dirname ++ "/" ++ leanpkg_toml_fn)

def construct_path (assg : assignment) : io (list string) := do
let assg := assg.fold [] (λ xs depname dirname, (depname, dirname) :: xs),
list.join <$> (assg.mmap $ λ ⟨depname, dirname⟩, construct_path_core depname dirname)

end leanpkg
