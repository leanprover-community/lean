/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Ebner
-/

prelude
import init.meta.tactic init.meta.derive init.meta.mk_dec_eq_instance init.meta.float

namespace feature_search

open tactic native

structure feature_cfg :=
(ignore_tc := tt)
(ignore_pi_domain := tt)
(ignore_type_args := tt)
(ignore_decidable := tt)
(ignore_conns := tt)

@[derive decidable_eq]
meta inductive feature
| const (n : name)
| arg (p : name) (c : name)

namespace feature

protected meta def to_string : feature → string
| (const n) := n.to_string
| (arg p c) := p.to_string ++ "→" ++ c.to_string

protected meta def repr : feature → string
| (const n) := "(const `" ++ n.to_string ++ ")"
| (arg p c) := "(arg `" ++ p.to_string ++ " `" ++ c.to_string ++ ")"

meta instance : has_to_string feature := ⟨feature.to_string⟩
meta instance : has_repr feature := ⟨feature.repr⟩
meta instance : has_to_tactic_format feature := ⟨λ f, pure f.to_string⟩
meta instance : has_to_format feature := ⟨λ f, f.to_string⟩

end feature

meta constant feature_vec : Type

namespace feature_vec

meta constant of_expr (env : environment) (e : expr) (cfg : feature_cfg := {}) : feature_vec
meta constant of_exprs (env : environment) (es : list expr) (cfg : feature_cfg := {}) : list feature_vec

protected meta constant union (a b : feature_vec) : feature_vec
meta instance : has_union feature_vec := ⟨feature_vec.union⟩

protected meta constant isect (a b : feature_vec) : feature_vec
meta instance : has_inter feature_vec := ⟨feature_vec.isect⟩

meta def of_proof (prf : expr) (cfg : feature_cfg := {}) : tactic feature_vec := do
ty ← infer_type prf,
env ← get_env,
pure $ of_expr env ty cfg

meta def of_thm (n : name) (cfg : feature_cfg := {}) : tactic feature_vec := do
decl ← get_decl n,
env ← get_env,
pure $ of_expr env decl.type cfg

protected meta constant to_list (fv : feature_vec) : list feature

meta instance : has_to_string feature_vec := ⟨to_string ∘ feature_vec.to_list⟩
meta instance : has_repr feature_vec := ⟨repr ∘ feature_vec.to_list⟩
meta instance : has_to_tactic_format feature_vec := ⟨pp ∘ feature_vec.to_list⟩
meta instance : has_to_format feature_vec := ⟨to_fmt ∘ feature_vec.to_list⟩

end feature_vec

meta constant feature_stats : Type

namespace feature_stats

meta constant of_feature_vecs (fvs : list feature_vec) : feature_stats
meta constant idf (fs : feature_stats) (f : feature) : float
meta constant norm (fs : feature_stats) (fv : feature_vec) : float
meta constant dotp (fs : feature_stats) (fv1 fv2 : feature_vec) : float
meta constant cosine_similarity (fs : feature_stats) (fv1 fv2 : feature_vec) : float
meta constant features (fs : feature_stats) : list feature

meta def features_with_idf (fs : feature_stats) : list (feature × float) :=
fs.features.map (λ f, (f, fs.idf f))

meta instance : has_to_string feature_stats := ⟨to_string ∘ feature_stats.features_with_idf⟩
meta instance : has_repr feature_stats := ⟨repr ∘ feature_stats.features_with_idf⟩
meta instance : has_to_tactic_format feature_stats := ⟨pp ∘ feature_stats.features_with_idf⟩
meta instance : has_to_format feature_stats := ⟨to_fmt ∘ feature_stats.features_with_idf⟩

end feature_stats

meta constant predictor : Type

meta constant predictor.predict (p : predictor) (goal : feature_vec) (max_results : ℕ) :
  list (name × float)

@[derive decidable_eq]
inductive predictor_type
| knn | mepo | bayes

structure predictor_cfg extends feature_cfg :=
(type := predictor_type.bayes)

end feature_search

open feature_search
meta constant environment.mk_predictor (env : environment) (cfg : predictor_cfg := {}) : predictor
