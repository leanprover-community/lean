class ring (α) extends has_one α

set_option trace.class_instances true
-- this should only synthesize `has_one α` once,
-- the second time it should already be cached
example (α : Type) [ring α] (h : (1 : α) = 1) :
true := trivial