prelude

import init.data.nat.basic

noncomputable theory

constant some_type : Type
constants foo bar : some_type

/-
  Test that notation with a high priority is used by the pretty-printer,
  regardless of the order in which they are declared.
-/
section
  notation [priority 2000] `high_before_low` := foo
  notation [priority 1] `low_after_high` := foo

  def test_high_before_low := foo
  #print test_high_before_low
end

section
  notation [priority 1] `low_before_high` := bar
  notation [priority 2000] `high_after_low` := bar

  def test_high_after_low := bar
  #print test_high_after_low
end
