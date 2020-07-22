class ring (α) extends has_one α

variables (α : Type) [ring α]
set_option trace.class_instances true
-- this should only synthesize `has_one α` once,
-- the second time it should already be cached
#check (1 : α) = 1