set_option trace.type_context_cache true
set_option trace.class_instances true

-- The following declaration should only do two type class searches, and each
-- only once: `has_one ℕ` and `has_add ℕ`
def foo : combinator.K ℕ (1 + 1 + 1) :=
show ℕ, from 1 + 1 + 1