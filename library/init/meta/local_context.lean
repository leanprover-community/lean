prelude
import init.meta.name init.meta.expr
meta structure local_decl :=
(unique_name : name)
(pp_name : name)
(type : expr)
(value : option expr)
(bi : binder_info)
(idx : nat)

/-- A local context is a list of local constant declarations.
    Each metavariable in a metavariable context holds a local_context
    to declare which locals the metavariable is allowed to depend on. -/
meta constant local_context : Type
namespace local_context
/-- Add a new local constant to the lc. The new local has an unused unique_name. Fails when the type depends on local constants that are not present in the context.-/
meta constant mk_local (pretty_name : name) (type : expr) (bi : binder_info) : local_context → option (expr × local_context)
meta constant get_local_decl : name → local_context → option local_decl
meta constant get_local : name → local_context → option expr
meta constant is_subset : local_context → local_context → bool
meta constant fold {α : Type} (f : α → expr → α): α → local_context → α
meta def to_list : local_context → list expr := list.reverse ∘ fold (λ acc e, e :: acc) []
meta def to_format : local_context → format := to_fmt ∘ to_list
meta instance lc_has_to_format : has_to_format local_context := ⟨to_format⟩
end local_context