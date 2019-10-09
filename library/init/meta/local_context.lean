prelude
import init.meta.name init.meta.expr
meta structure local_decl :=
(unique_name : name)
(pp_name : name)
(type : expr)
(value : option expr)
(bi : binder_info)
(idx : nat)

/-- Local context. -/
meta constant lc : Type

namespace lc
  /-- Add a new local constant to the lc. The new local has an unused unique_name. Fails when the type depends on local constants that are not present in the context.-/
  meta constant mk_local (pretty_name : name) (type : expr) (bi : binder_info) : lc → option (expr × lc)
  -- meta constant mk_local_decl_assigned (pretty_name : name) (type : expr) (value : expr) : lc expr
  meta constant get_local_decl : name → lc → option local_decl
  meta constant get_local : name → lc → option expr
  -- /-- Removes the local decl with the given unique name. Will fail if other decls in the context depend on it. -/
  -- meta constant clear : name → lc → lc
  -- /-- Removes the local with the given unique name and recursively clears decls that depend on it. -/
  -- meta constant clear_recursive : name → lc → lc
  meta constant is_subset : lc → lc → bool
  meta constant fold {α : Type} (f : α → expr → α): α → lc → α
  meta def to_list : lc → list expr := list.reverse ∘ fold (λ acc e, e :: acc) []
  meta def to_format : lc → format := to_fmt ∘ to_list
  meta instance lc_has_to_format : has_to_format lc := ⟨to_format⟩
end lc
