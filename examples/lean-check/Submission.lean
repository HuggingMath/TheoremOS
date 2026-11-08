namespace Tutorial

theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

theorem zero_add (n : Nat) : 0 + n = n := by
  exact Nat.zero_add n

end Tutorial

#print axioms Tutorial.add_zero
#print axioms Tutorial.zero_add
