add_library(tactic OBJECT occurrences.cpp kabstract.cpp tactic_state.cpp
  tactic_log.cpp intro_tactic.cpp revert_tactic.cpp clear_tactic.cpp
  app_builder_tactics.cpp subst_tactic.cpp exact_tactic.cpp
  change_tactic.cpp assert_tactic.cpp apply_tactic.cpp
  fun_info_tactics.cpp congr_lemma_tactics.cpp match_tactic.cpp
  ac_tactics.cpp induction_tactic.cpp cases_tactic.cpp
  generalize_tactic.cpp rewrite_tactic.cpp unfold_tactic.cpp
  hsubstitution.cpp gexpr.cpp elaborate.cpp init_module.cpp
  simp_result.cpp user_attribute.cpp eval.cpp
  simp_lemmas.cpp eqn_lemmas.cpp dsimplify.cpp simplify.cpp
  vm_monitor.cpp destruct_tactic.cpp hole_command.cpp
  elaborator_exception.cpp algebraic_normalizer.cpp tactic_evaluator.cpp
  vm_local_context.cpp
  vm_type_context.cpp)
if(EMSCRIPTEN)
add_dependencies(tactic gmp)
endif()
