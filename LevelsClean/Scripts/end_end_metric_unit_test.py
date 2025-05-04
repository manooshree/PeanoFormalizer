from evaluate import evaluate_proof



# Unit test 0a
# all correct
predicted_fl = ["rfl"]
true_fl = ["rfl"]
fl_theorem_statement = "theorem add_comm_helper1 (a : ℕ) : a + 0 = 0 + a := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 1
print("Unit test 0a done")

# Unit test 0b
# incorrect
predicted_fl = ["rfl"]
true_fl = ["refl"]
fl_theorem_statement = "theorem add_comm_helper2 (a : ℕ) : a + 0 = 0 + a := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 0
print("Unit test 0b done")


# Unit test 1
# all correct
predicted_fl = ["intro h", "rw [← is_zero_succ a]", "apply succ_inj at h", "exact h"]
true_fl = ["intro h", "rw [← is_zero_succ a]", "apply succ_inj at h", "exact h"]
fl_theorem_statement = "theorem tester1 (a b : ℕ) : a = b := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 4
print("Unit test 1 done")


# Unit test 2 
# testing with spaces
predicted_fl = ["rw [add_zero]", "rw [zero_add]", "rfl" ]
true_fl = [" rw [add_zero]", "rw [zero_add] ", " rfl" ]
fl_theorem_statement = "theorem add_comm_test4 (a : ℕ) : a + 0 = 0 + a := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 3
print("Unit test 2 done")


# Unit test 3
# exchange order within rws
predicted_fl = [" rw [add_zero, zero_add]", " rfl" ]
true_fl = ["rw [zero_add, add_zero]", "rfl"]
fl_theorem_statement = "theorem add_comm_test5 (a : ℕ) : a + 0 = 0 + a := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 2
print("Unit test 3 done")

# Unit test 4 
# repeat vs two rw's
predicted_fl = [" rw [add_zero]", " rfl" ]
true_fl = ["repeat rw [add_zero]", "rfl"]
fl_theorem_statement = "theorem add_comm_test6 (a : ℕ) : a + 0 = a + 0 := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 2
print("Unit test 4 done")

# Unit test 5
# comma seperated rws vs two rw's when its in a wrong case
predicted_fl = [" rw [add_zero]", " rfl" ]
true_fl = ["rw [zero_add], rw [add_zero]", "rfl"]
fl_theorem_statement = "theorem add_comm_test7 (a : ℕ) : a + 0 = 0 + a := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 1
print("Unit test 5 done")


# ASK
# Unit test 6
# Random NL showing up within FL but things after that are correct
predicted_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", """This statement in Lean syntax would be:
 

 rw [add_comm a b]""", "rfl"]
fl_theorem_statement = "theorem add_left_comm8 (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6
print("Unit test 6 done")


# Unit test 7
# One step is wrong first
predicted_fl = ["rw [add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
fl_theorem_statement = "theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6
print("Unit test 7 done")

# Unit test 8
# One step is wrong not first
predicted_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
fl_theorem_statement = "theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6
print("Unit test 8 done")

# Unit test 9
# One step is wrong last
predicted_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "refl"]
fl_theorem_statement = "theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6
print("Unit test 9 done")


# ASK
# Unit test 10
# One step is wrong with random NL instead
predicted_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "The formalized version of the natural language statement is not correct, as it implies replacing the original theorem with a new one. Lean does not support this operation. The original goal cannot be modified to prove `succ 0 = _dev_1`. The correct approach would usually involve using `cases` to further break down the original theorem and prove each case separately. I'm sorry, but I can't provide the correct Lean command without more context of the proof.", 
           "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "refl"]
fl_theorem_statement = "theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 5
print("Unit test 10 done")


# ASK
# Unit test 11
# One step is wrong with two steps instead of one seperated by a enter
predicted_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", """rfl
           rw [← add_assoc]""", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
fl_theorem_statement = "theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6
print("Unit test 11 done")

# ASK
# Unit test 12
# One step is wrong with the LLM output having "Output: "
predicted_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", """The formalized version of the natural language statement is:
 

 rfl""", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
fl_theorem_statement = "theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6
print("Unit test 12a done")


# ASK
# Unit test 12
# One step is wrong with the LLM output having "Output: "
predicted_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", """The formalized version of the natural language statement is:
 

 rfl""", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
fl_theorem_statement = "theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6
print("Unit test 12b done")

# Unit test 13
# One step is wrong with the LLM output having "Output: "
predicted_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", "rfl", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
true_fl = ["rw [← add_assoc]", "rw [add_comm a b, add_assoc]", """The formalized version of the natural language statement is:
 

 rfl""", "rw [← add_assoc]", "rw [← add_assoc]", "rw [add_comm a b]", "rfl"]
fl_theorem_statement = "theorem add_left_comm (a b c : ℕ) : a + (b + c) = b + (a + c) := by"
results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6
print("Unit test 13 done")




# ASK
# Unit test 14
# case where we have comma seperated tactics
true_fl = ["cases x with y", "left", "rfl", "cases y with z", "right", "left", "rw [one_eq_succ_zero]", "rfl", "rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢", "apply succ_le_succ at hx", "apply succ_le_succ at hx", "apply le_zero at hx", "rw [hx]", "right", "right", "rfl"]
predicted_fl =  ["cases x with y", "left, rfl, left, right, rw [add_comm]", "rfl", "cases y with z", "right", "left", "rw [one_eq_succ_zero]", "rfl", "rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢", "apply succ_le_succ at hx", "apply succ_le_succ at hx", "apply le_zero at hx", "rw [hx]", "right", "right", "rfl"]
fl_theorem_statement = "theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 16
print("Unit test 14 done")


# ASK
# Unit test 15
# long proof random things wrong in the middle
true_fl = ["cases x with y", "left", "rfl", "cases y with z", "right", "left", "rw [one_eq_succ_zero]", "rfl", "rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢", "apply succ_le_succ at hx", "apply succ_le_succ at hx", "apply le_zero at hx", "rw [hx]", "right", "right", "rfl"]
predicted_fl =["cases x with y", "right", "rfl", "cases y with z", "left", "right", "rw [two_eq_succ_one]", "rfl", "rw [two_eq_succ_one, one_eq_succ_zero]", "apply succ_le_succ at hx", "apply succ_le_succ at hx", "apply add_comm at hx", "rw [hx]", "right", "left", "rfl"]
fl_theorem_statement = "theorem le_two (x : ℕ) (hx : x ≤ 2) : x = 0 ∨ x = 1 ∨ x = 2 := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 9
print("Unit test 15 done")


# Unit test 16
# checking add_comm vs add_comm a b
true_fl = ["rw [add_comm]"]
predicted_fl = ["rw [add_comm a b]"]
fl_theorem_statement = "theorem add_comm_test (a : ℕ) : a + b = b + a := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 1
print("Unit test 16 done")

# Unit test 17
# checking nthrewrite
true_fl = ["nth_rewrite 3 [← add_zero 0]"]
predicted_fl = ["rw [add_zero 0]"]
fl_theorem_statement = "theorem add_comm_test (a : ℕ) : 0 + 0 = 0 + 0 := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 0
print("Unit test 17 done")

# Unit test 18
# checking nthrewrite
true_fl = ["nth_rewrite 3 [← add_zero 0]"]
predicted_fl = ["rw [add_zero 0]"]
fl_theorem_statement = "theorem add_comm_test (a : ℕ) : 0 + 0 = 0 + 0 := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 0
print("Unit test 18 done")

# Unit test 19
# checking nthrewrite in a case where its the same as rw
true_fl = ["nth_rewrite 1 [add_zero a]"]
predicted_fl = ["rw [add_zero a]"]
fl_theorem_statement = "theorem add_comm_test (a : ℕ) : a + 0 = 0 := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 1
print("Unit test 19 done")

# Unit test 19b
# checking nthrewrite in a case where its the same as rw part 2
true_fl = ["nth_rewrite 1 [add_zero a]"]
predicted_fl = ["rw [add_zero]"]
fl_theorem_statement = "theorem add_comm_test (a : ℕ) : a + 0 = 0 := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 1
print("Unit test 19 done")

# Unit test 20
# checking nthrewrite in a case where its the same as rw part 3
true_fl = ["nth_rewrite 1 [add_zero a], nth_rewrite 2 [add_zero a]"]
predicted_fl = ["repeat rw [add_zero]"]
fl_theorem_statement = "theorem add_comm_test (a : ℕ) : a + 0 + 0 = 0 := by"

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 0
print("Unit test 20 done")


# Unit test 21
# Testing succ_eq_add_one proof steps
fl_theorem_statement = "theorem succ_eq_add_one (n : ℕ) : succ n = n + 1 := by"
true_fl = [
    "rw [← add_zero n]",
    "rw [one_eq_succ_zero]",
    "rw [add_succ]",
    "rw [add_zero (n+0)]",
    "rfl",
    "rw [one_eq_succ_zero]",
    "rw [← add_zero n]",
    "rw [add_succ]",
    "rw [add_zero]",
    "rw [add_zero]",
    "rfl"
]

predicted_fl = [
    "rw [← add_zero n]",
    "rw [one_eq_succ_zero]",
    "rw [add_succ]",
    "rw [add_zero]",
    "rw [add_zero]",
    "rw [one_eq_succ_zero]",
    "rw [← add_zero n, ← add_zero n]",
    "rw [add_succ]",
    "rw [add_zero]",
    "rw [add_zero]",
    "rw [add_zero]"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful < 11  # Not all steps will be successful
print("Unit test 21 done")


# Unit test 22
# Testing a proof that was expected to work from experiments in autoformalizer exp-9
fl_theorem_statement = "theorem zero_pow_succ (m : ℕ) : 0 ^ (succ m) = 0 := by"
true_fl = [
    "induction m with d hd",
    "The given natural language statement is incorrect and can't be formalized to a valid Lean code. As such, there is no corresponding line of Lean code.",
    "rw [mul_zero]",
    "rfl",
    "rw [pow_succ]",
    "rw [pow_succ, hd, mul_zero]",
    "rw [mul_zero]",
    "rfl"
]

predicted_fl = [
    "induction m with d hd",
    "rw [pow_succ]",
    "rw [mul_zero]",
    "rfl",
    "rw [pow_succ]",
    "rw [hd]",
    "rw [mul_zero]",
    "rfl"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 6  # Not all steps will be successful
print("Unit test 22 done")




# Unit test 23
# Testing cases and intro tactics for add_right_eq_zero theorem
fl_theorem_statement = "theorem add_right_eq_zero_tester (a b : ℕ) : a + b = 0 → a = 0 := by"
true_fl = ["cases b with d",
    "intro h",
    "rw [← add_zero a]",
    "exact h",
    "intro h",
    "rw [add_succ] at h",
    "symm at h",
    "apply zero_ne_succ at h"
]


predicted_fl = [
    "cases b with d",
    "intro h₀",
    "rw [zero_add] at h₀",
    "The formalized version of the natural language statement is:\n \n `exact h`",
    "intro h",
    "rw [add_succ] at h₀",
    "symm at h",
    "cases h"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 4  # Not all steps will be successful
print("Unit test 23 done")


# VARIABLE DIFFERENT TESTS


# Unit test 24
# testing variable changes and lots of small equivalent tactic changes
fl_theorem_statement = "theorem add_right_eq_zero_testings (a b : ℕ) : a + b = 0 → a = 0 := by"
true_fl = ["cases b with d",
    "intro h",
    "rw [← add_zero a]", # nth_rewrite 1 [← add_zero a]
    "exact h",
    "intro h",
    "rw [add_succ] at h",
    "symm at h",
    "apply zero_ne_succ at h",
    "tauto"
]


predicted_fl = [
    "cases b with d",
    "intro h₀",
    "rw [← add_zero a]",
    "exact h₀",
    "intro ha",
    "rw [add_succ] at ha",
    "symm at ha",
    "apply zero_ne_succ at ha",
    "tauto"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
print(num_successful, proof_is_correct)
assert proof_is_correct == True
assert num_successful == 9 # Not all steps will be successful

print("Unit test 24 done")


# Unit test 24b
# testing variable changes and lots of small equivalent tactic changes
fl_theorem_statement = "theorem add_right_eq_zero_testings (a b : ℕ) : a + b = 0 → a = 0 := by"
true_fl = ["cases b with d",
    "intro h",
    "rw [add_zero a] at h", # nth_rewrite 1 [← add_zero a]
    "exact h",
    "intro h",
    "rw [add_succ] at h",
    "symm at h",
    "apply zero_ne_succ at h",
    "tauto"
]


predicted_fl = [
    "cases b with d",
    "intro h₀",
    "rw [← add_zero a]",
    "exact h₀",
    "intro ha",
    "rw [add_succ] at ha",
    "symm at ha",
    "apply zero_ne_succ at ha",
    "tauto"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
print(num_successful, proof_is_correct)
assert proof_is_correct == False
assert num_successful == 8 # Not all steps will be successful

print("Unit test 24b done")


# Unit test 24c
# testing variable changes and lots of small equivalent tactic changes
fl_theorem_statement = "theorem add_right_eq_zero_testings (a b : ℕ) : a + b = 0 → a = 0 := by"
true_fl = ["cases b with d",
    "intro h",
    "nth_rewrite 1 [← add_zero a]",
    "exact h",
    "intro h",
    "rw [add_succ] at h",
    "symm at h",
    "apply zero_ne_succ at h",
    "tauto"
]


predicted_fl = [
    "cases b with d",
    "intro h₀",
    "rw [← add_zero a]",
    "exact h₀",
    "intro ha",
    "rw [add_succ] at ha",
    "symm at ha",
    "apply zero_ne_succ at ha",
    "tauto"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
print(num_successful, proof_is_correct)
assert proof_is_correct == True
assert num_successful == 9 # Not all steps will be successful

print("Unit test 24c done")


# Unit test 25
# testing add_comm proof with variable differences
fl_theorem_statement = "theorem add_comm_testings (a b : ℕ) : a + b = b + a := by"
true_fl = [
    "induction b with d hd",
    "rw [add_zero, zero_add]",
    "rfl",
    "rw [add_succ, succ_add]",
    "rw [hd]",
    "rfl"
]

predicted_fl = [
    "induction b with n ih",
    "rw [add_zero, zero_add]",
    "rfl",
    "rw [add_succ, succ_add]",
    "rw [ih]",
    "rfl"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 6  # All steps should be successful despite variable name differences
print("Unit test 25 done")


# Unit test 26
# testing le_two proof with variable differences
fl_theorem_statement = "theorem le_two_testers (x : ℕ) : x = 0 ∨ x = 1 ∨ x = 2 := by"
true_fl = [
    "cases x with y",
    "left",
    "rfl",
    "cases y with z",
    "right",
    "left",
    "rw [one_eq_succ_zero]",
    "rfl",
    "rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢",
    "apply succ_le_succ at hx",
    "apply succ_le_succ at hx",
    "apply le_zero at hx",
    "right",
    "rfl"
]

predicted_fl = [
    "cases x with y",
    "left",
    "rfl",
    "cases y with z",
    "right",
    "left",
    "rw [one_eq_succ_zero]",
    "rfl",
    "rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢",
    "apply succ_le_succ at hx",
    """The provided natural language statement does not directly correspond to a Lean code as the current state doesn't involve the natural number ""z"". However, the Lean version of the statement can generally be expressed as:
 

 apply succ_le_succ at hx""",
    """The natural language statement "-- Since z ≤ 0, using a theorem, z = 0." seems to be not applicable in the current state of the proof since there is no variable 'z' and we are not working on 'z ≤ 0'. Therefore, there is no corresponding Lean code for this statement given the current context.""",
    "right",
    "rfl"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 12  
print("Unit test 26 done")

# Unit test 27
# testing implication proof with different variable names but equivalent structure
fl_theorem_statement = "theorem exact_2_tester (p q : Prop) : p → q → p := by"
true_fl = [
    "intro h1",
    "intro h2",
    "exact h1"
]

predicted_fl = [
    "intro hp",
    "intro hq",
    "exact hp"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 3  # All steps should be successful despite variable name differences
print("Unit test 27 done")

# Unit test 28
# testing more complex implication proof with different variable names
fl_theorem_statement = "theorem contrapose_tester (p q : Prop) : (p → q) → (¬q → ¬p) := by"
true_fl = [
    "intro h",
    "intro h1",
    "intro h2",
    "apply h1",
    "apply h",
    "exact h2"
]

predicted_fl = [
    "intro hpq",
    "intro hnq",
    "intro hp",
    "apply hnq",
    "apply hpq",
    "exact hp"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 6  # All steps should be successful despite variable name differences
print("Unit test 28 done")

# COMMENT
# # Unit test 29
# # testing implication proof with different variable names and slightly different structure
# fl_theorem_statement = "theorem modus_ponens_tester (p q : Prop) : p → (p → q) → q := by"
# true_fl = [
#     "intro hp",
#     "intro hpq",
#     "apply hpq",
#     "exact hp"
# ]

# predicted_fl = [
#     "intro h1",
#     "intro h",
#     "have h2 := h h1",
#     "exact h2"
# ]

# results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
# print(tactic_accuracy, proof_is_correct, num_successful)
# assert proof_is_correct == False  # Different structure should make it fail
# assert num_successful == 2  # Not all steps should be successful
# print("Unit test 29 done")


# Unit test 30
# Testing a proof with nth_rewrite vs regular rewrite (in the middle of proof)
fl_theorem_statement = "theorem add_right_comm_tester (a b c : ℕ) : a + b + c = a + c + b := by"
true_fl = [
    "rw [add_assoc]",
    "rw [add_comm b c]",
    "rw [← add_assoc]",
    "rfl"
]

predicted_fl = [
    "rw [add_assoc]",
    "nth_rewrite 1 [add_comm b c]",
    "rw [← add_assoc]",
    "rfl"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == True
assert num_successful == 4  # Should be successful despite nth_rewrite vs rw difference
print("Unit test 30 done")

# Unit test 31
# we should consider handing this but later problem
# Testing a proof with comma-separated tactics vs individual tactics
fl_theorem_statement = "theorem add_succ_comm_tester (a b : ℕ) : succ a + b = a + succ b := by"
true_fl = [
    "rw [succ_add], rw [add_succ]",
    "rfl"
]

predicted_fl = [
    "rw [succ_add, add_succ]",
    "rfl"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
assert proof_is_correct == False
assert num_successful == 1 # Should count as 3 successful steps despite being in 2 lines
print("Unit test 31 done")

# Unit test 32
# Testing a proof with different but equivalent approaches
fl_theorem_statement = "theorem mul_zero_tester (n : ℕ) : n * 0 = 0 := by"
true_fl = [
    "induction n with d hd",
    "rw [zero_mul]",
    "rfl",
    "rw [succ_mul]",
    "rw [hd]",
    "rw [add_zero]",
    "rfl"
]

predicted_fl = [
    "induction n with d hd",
    "rw [zero_mul]",
    "rfl",
    "rw [succ_mul]",
    "rw [ih]",  # Wrong variable name
    "rw [add_zero]",
    "rfl"
]

results, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_fl, true_fl, fl_theorem_statement, [])
print(num_successful, proof_is_correct)
assert proof_is_correct == False
assert num_successful == 6  # Should fail at the 5th step due to wrong variable name
print("Unit test 32 done")


