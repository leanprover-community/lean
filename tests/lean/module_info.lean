open tactic

#eval module_info.get_all

#eval (module_info.resolve_module_name `data.dlist).backn 10

#eval (environment.from_imported_module_name `data.dlist).contains `dlist

meta def dlist_mod_until_to_list_empty : tactic environment := do
e ← get_env,
pure $ e.import_until_decl (module_info.of_module_name `data.dlist) `dlist.to_list_empty

-- last declaration before to_list_empty is included
#eval flip environment.contains `dlist.of_list_to_list <$> dlist_mod_until_to_list_empty >>= trace

-- but to_list_empty is not
#eval flip environment.contains `dlist.to_list_empty <$> dlist_mod_until_to_list_empty >>= trace

-- do not do this
#eval by do
e ← get_env,
set_env_core $ e.import' (module_info.of_module_name `data.dlist),
exact `("imported")

#eval get_decl `dlist.to_list >>= trace ∘ declaration.type

-- double imports will just fail
#eval do
e ← get_env,
set_env_core $ e.import' (module_info.of_module_name `data.dlist)
