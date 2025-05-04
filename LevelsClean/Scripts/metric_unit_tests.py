# Unit tests for the check_if_correct function from metric.py
# This file tests various scenarios to ensure the function correctly identifies
# when two Lean4 tactics are equivalent despite superficial differences

# Import the function we're testing with an alias
from metric import check_if_correct as is_correct

# Test case: Spaces are stripped from tactics
# Should return True when tactics are the same except for leading spaces
assert is_correct(" exact h", "exact h", "",
                  '''y x : ℕ
 h : 0 + x = 0 + y + 2
 ⊢ x = y + 2'''
 ) == True

# Test case: Whitespace differences between tactics
# Should return True when tactics have different whitespace but produce the same goal state
assert is_correct("left", "rfl \n left", '''"case zero.h
 hx : 0 ≤ 2
 ⊢ 0 = 0
 case succ
 y : ℕ
 hx : succ y ≤ 2
 ⊢ succ y = 0 ∨ succ y = 1 ∨ succ y = 2"''', '''"case zero.h
 hx : 0 ≤ 2
 ⊢ 0 = 0
 case succ
 y : ℕ
 hx : succ y ≤ 2
 ⊢ succ y = 0 ∨ succ y = 1 ∨ succ y = 2"''') == True

# Test case: Different variable names in induction (currently commented out)
# Should return True when tactics use different variable names but are functionally equivalent
assert is_correct("induction n with a ha", "induction n with d hd", '''case zero
 ⊢ 0 * 0 = 0
 case succ
 a : ℕ
 ha : 0 * a = 0
 ⊢ 0 * succ a = 0
 ''', '''case zero
 ⊢ 0 * 0 = 0
 case succ
 d : ℕ
 hd : 0 * d = 0
 ⊢ 0 * succ d = 0''') == True

# Test case: Same tactics but different goals
# Should return True when different tactics are used but they produce the same goal state
assert is_correct("rfl", "rfl", '''"case succ
 h : ℕ
 hd : 0 ^ succ h = 0
 ⊢ 0 ^ succ (succ h) = 0"''', '''"case zero
 ⊢ 0 ^ succ 0 = 0
 case succ
 d : ℕ
 hd : 0 ^ succ d = 0
 ⊢ 0 ^ succ (succ d) = 0"''') == True

# Test case: Matching tactics but different goals
# Should return True when tactics match exactly even if goals are different
assert is_correct("rw [add_zero]", "rw [add_zero]", "a = a", "b + a = b") == True

# Test case: Different tactics and different goals
# Should return False when both tactics and goals are different
assert is_correct("rw [add_zero]", "rfl", """ a b c : ℕ
 ⊢ a + b + c = b + (a + c) """, "") == False

# Test case: Empty predicted tactic
# Should return False when the predicted tactic is empty
assert is_correct("rw [add_zero]", "", "a = a", "") == False

# Test case: Rewrite with repeats - different results
# Should return False when repeating a rewrite produces different results
assert is_correct("rw [zero_add] at h", "rw [zero_add, zero_add] at h", '''y x : ℕ
 h : x = 0 + y + 2
 ⊢ x = y + 2''', '''y x : ℕ
 h : 0 + x = 0 + y + 2
 ⊢ x = y + 2''') == False

# Test case: Rewrite with repeats - same results
# Should return True when different ways of expressing repeated rewrites produce the same result
assert is_correct("repeat rw [zero_add] at h", "rw [zero_add, zero_add] at h", '''y x : ℕ
 h : x = y + 2
 ⊢ x = y + 2''', '''y x : ℕ
 h : x = y + 2
 ⊢ x = y + 2''') == True

# Test case: Different hypothesis names but same state
# Should return True when hypothesis names differ but the state is functionally the same
assert is_correct("repeat rw [zero_add] at h", "rw [zero_add, zero_add] at h1", '''y x : ℕ
 h : x = y + 2
 ⊢ x = y + 2''', '''y x : ℕ
 h1 : x = y + 2
 ⊢ x = y + 2''') == True

# Test case: Different operations (addition vs multiplication)
# Should return False when goals involve different operations
assert is_correct("rw [add_mul]", "rw [add_comm]", '''y x : ℕ
 ⊢ x + y = y + x''', '''y x : ℕ
 ⊢ x * y = y * x''') == False

# Test case: Equality vs inequality
# Should return False when one goal uses equality and the other uses inequality
assert is_correct("rw [mul_add]", "intro hb", '''a b : ℕ
 h : a * b = 0
 hd : b = 0
 ⊢ False''', '''a b : ℕ
 h : a * b ≠ 0
 hb : b = 0
 ⊢ False''') == False

# Test case: Different variable names in intro
# Should return True when intro tactics use different variable names
assert is_correct("intro hd", "intro hb", '''a b : ℕ
 h : a * b ≠ 0
 hd : b = 0
 ⊢ False''', '''a b : ℕ
 h : a * b ≠ 0
 hb : b = 0
 ⊢ False''') == True

# Test case: Same tactic with error result
# Should handle error cases correctly when tactics are the same but produce errors
assert is_correct(" symm at h", "symm at h", '''"case succ
 a d : ℕ
 h : 0 = succ (a + d)
 ⊢ a = 0"''',"error")

# Test case: Same tactic with trailing spaces and error result
# Should handle error cases correctly when tactics differ only in trailing spaces
assert is_correct(" symm at h", "symm at h  ", '''"case succ
 a d : ℕ
 h : 0 = succ (a + d)
 ⊢ a = 0"''',"error")

# Test case: Variable renaming throughout
# Should return True when all variables are consistently renamed
assert is_correct("rw [add_comm]", "rw [add_mul]", """a b : ℕ
 ha : a * b ≠ 0
 h : b = 0
 ⊢ False""", """c d : ℕ
 h : c * d ≠ 0
 hd : d = 0
 ⊢ False""") == True

# Test case: Inconsistent variable renaming
# Should return False when variable renaming is not consistent
assert is_correct("rw [add_comm]", "rw [add_mul]", """c d : ℕ
 ha : d * c ≠ 0
 h : d = 0
 ⊢ False""", """a b : ℕ
 h : a * b ≠ 0
 hd : b = 0
 ⊢ False""") == False

# Test case: Inconsistent variable usage
# Should return False when variables are used inconsistently between states
assert is_correct("rw [add_comm]", "rw [add_mul]", """a b: ℕ
 ha : b * b ≠ 0
 h : a = 0
 ⊢ False""", """c d : ℕ
 h : c * c ≠ 0
 hd : d = 0
 ⊢ False""") == False

# Test case: Different hypothesis names
# Should return True when hypothesis names differ but are used consistently
assert is_correct("rw [add_comm]", "rw [add_mul]", """x y: ℕ
 ha : x * y = 0
 h : y = 0
 ⊢ False""", """a b: ℕ
 h1 : a * b = 0
 h : b = 0
 ⊢ False""") == True

# Test case: Different values in hypotheses
# Should return False when hypothesis values differ between states
assert is_correct("rw [add_comm a b]", "rw [add_mul]", """x y: ℕ
 ha : x * y = 0
 h : y = 1
 ⊢ False""", """a b: ℕ
 h1 : a * b = 0
 h : b = 0
 ⊢ False""") == False


# Test case: Consistent variable renaming with different hypothesis names
# Should return True when variables and hypotheses are consistently renamed
assert is_correct("rw [add_comm a b]", "rw [add_mul]", """x y: ℕ
 ha : x * y = 0
 hb : y = 0
 ⊢ False""", """a b: ℕ
 h1 : a * b = 0
 h : b = 0
 ⊢ False""") == True


# Test case: Variable renaming with numeric suffixes
# Should return True when variables with numeric suffixes are consistently renamed
assert is_correct("rw [add_comm a b]", "rw [add_mul]", """x1 y: ℕ
 ha : x1 * y = 0
 hb : y = 0
 ⊢ False""", """a b: ℕ
 h1 : a * b = 0
 h : b = 0
 ⊢ False""") == True

# Modified one_ne_zero_dev_2
assert is_correct("intro h","intro h1","""
h : 1 = 0
⊢ False
""",
"""
h1 : 1 = 0
⊢ False
""")

# Modification of add_left_comm_dev_1
# We want this to fail; the goal of this is to make sure it still fails when there are lots of variables
assert not is_correct("rw [add_comm a b, add_assoc]","rw [add_comm b, add_assoc]","""
a b c : ℕ
⊢ b + (a + c) = b + (a + c)
""",
"""
a b c : ℕ
⊢ a + (b + c) = a + c + b
""")

# Modification of one_ne_zero_dev_1
# NNG4 has naming hygine disabled, so this to check to make sure that the lack of naming information
# in the tactics themselves doesn't break anything
assert is_correct("intro h", "intro _","""
h : 1 = 0
⊢ False
""", """
a : 1 = 0
⊢ False
""")

# Modification of add_right_cancel
assert is_correct("induction n with d hd", "induction n with _ hd", """
case zero
a b : ℕ
⊢ a + 0 = b + 0 → a = b
case succ
a b d : ℕ
hd : a + d = b + d → a = b
⊢ a + d.succ = b + d.succ → a = b
""","""
case zero
a b : ℕ
⊢ a + 0 = b + 0 → a = b
case succ
a b n_1 : ℕ
hd : a + n_1 = b + n_1 → a = b
⊢ a + n_1.succ = b + n_1.succ → a = b
""")

# The metric should still pass when both tactics resulted in all goals being closed
assert is_correct("random_tactic_1","random_tactic_2","","\n")

# Modification of mul_left_cancel_dev_1
# This is to make sure that a forall in the proof state doesn't break anything
assert is_correct("induction b with d hd generalizing c", "induction b with k hk generalizing c", """
case zero
a : ℕ
ha : a ≠ 0
c : ℕ
h : a * 0 = a * c
⊢ 0 = c
case succ
a : ℕ
ha : a ≠ 0
d : ℕ
hd : ∀ (c : ℕ), a * d = a * c → d = c
c : ℕ
h : a * d.succ = a * c
⊢ d.succ = c
""","""
case zero
a : ℕ
ha : a ≠ 0
c : ℕ
h : a * 0 = a * c
⊢ 0 = c
case succ
a : ℕ
ha : a ≠ 0
k : ℕ
hk : ∀ (c : ℕ), a * k = a * c → k = c
c : ℕ
h : a * k.succ = a * c
⊢ k.succ = c
""")

# Another modification of mul_left_cancel_dev_1, this time further down the proof and assuming the
# above change was made in one of the proofs
assert is_correct("cases c with e he", "cases c with f hf", """
case succ.zero
a : ℕ
ha : a ≠ 0
d : ℕ
hd : ∀ (c : ℕ), a * d = a * c → d = c
h : a * d.succ = a * 0
⊢ d.succ = 0
case succ.succ
a : ℕ
ha : a ≠ 0
d : ℕ
hd : ∀ (c : ℕ), a * d = a * c → d = c
e : ℕ
h : a * d.succ = a * e.succ
⊢ d.succ = e.succ
""","""
case succ.zero
a : ℕ
ha : a ≠ 0
k : ℕ
hk : ∀ (c : ℕ), a * k = a * c → k = c
h : a * k.succ = a * 0
⊢ k.succ = 0
case succ.succ
a : ℕ
ha : a ≠ 0
k : ℕ
hk : ∀ (c : ℕ), a * k = a * c → k = c
f : ℕ
h : a * k.succ = a * f.succ
⊢ k.succ = f.succ
""")

# TOOD: Different variable names in each case (this might be tested by the shadowing test below)

# Another modification of add_right_cancel, this time to test variable shadowing
# This also tests variable names different in different cases 
assert is_correct("induction n with d hd", "induction n with a b", """
case zero
a b : ℕ
⊢ a + 0 = b + 0 → a = b
case succ
a b d : ℕ
hd : a + d = b + d → a = b
⊢ a + d.succ = b + d.succ → a = b
""","""
case zero
a b : ℕ
⊢ a + 0 = b + 0 → a = b
case succ
a✝ b✝ a : ℕ
b : a✝ + a = b✝ + a → a✝ = b✝
⊢ a✝ + a.succ = b✝ + a.succ → a✝ = b✝
""")


# Modification of succ_ne_zero
# Supposed to check that False and True are not being treated as a variable
assert not is_correct("rw [is_zero_zero]","apply False.elim","""
a : ℕ
h : a.succ = 0
⊢ True
""",
"""
a : ℕ
h : a.succ = 0
⊢ False
""")

# Yet another modification of mul_left_cancel_dev_1, this time to check variable shadowing inside
# a forall block
assert is_correct("induction b with d hd generalizing c", "induction b with c hc generalizing c", """
case zero
a : ℕ
ha : a ≠ 0
c : ℕ
h : a * 0 = a * c
⊢ 0 = c
case succ
a : ℕ
ha : a ≠ 0
d : ℕ
hd : ∀ (c : ℕ), a * d = a * c → d = c
c : ℕ
h : a * d.succ = a * c
⊢ d.succ = c
""","""
case zero
a : ℕ
ha : a ≠ 0
c : ℕ
h : a * 0 = a * c
⊢ 0 = c
case succ
a : ℕ
ha : a ≠ 0
c✝ : ℕ
hc : ∀ (c : ℕ), a * c✝ = a * c → c✝ = c
c : ℕ
h : a * c✝.succ = a * c
⊢ c✝.succ = c
""")

# Run all tests and report success if they all pass
if __name__ == "__main__":
    print("All tests passed!")