from Model import gpt_prompt, parse_lean_proof, parse_nl_proof
import sys
import os
from lean_compile import lean_compile

# Move to LeanTutor directory once at startup
script_dir = os.path.dirname(os.path.abspath(__file__))
os.chdir(os.path.join(script_dir, "../../../"))

# Sample Lean proof
lean_proof = '''
-- Induct on n, with d = 0 as the base case and the inductive hypothesis 0 + d = d. There are now two proof goals, prove base case: 0 + 0 = 0, and inductive step: 0 + succ (d) = succ (d)
  induction n with d hd
-- First prove base case. Reduce LHS 0 + 0 = 0.
  · rw [add_zero]
-- Prove LHS and RHS are equal, 0 = 0, completing base case
    rfl
-- Now prove inductive step. Rewrite 0 + succ d = succ (0 + d)
  · rw [add_succ]
-- Simplify RHS succ (0 + d) = succ(d) using the inductive hypothesis.
    rw [hd]
-- Prove LHS and RHS are equal, succ(d) = succ(d), completing the proof
    rfl
'''

if "stored_tactics" not in globals():
    globals()["stored_tactics"] = [] 

def process_proof(proof_lines, theorem_name, theorem_header):
    stored_tactics = globals()["stored_tactics"] 
    if not stored_tactics:  
        stored_tactics.append(theorem_header)

    proof_pairs = parse_nl_proof(proof_lines)
    print("Theorem header", theorem_header)
    
    for i, (nl, _) in enumerate(proof_pairs):
        print(f"\n🔹 Processing Step {i+1}/{len(proof_pairs)}\n")
        print(f"NL: {nl}")

        

        predicted_tactic = gpt_prompt(nl)
        globals()["stored_tactics"].append(predicted_tactic)

        print("\n=== Debugging Generated Tactics Before Compilation ===")
        print(stored_tactics)  
        print("\n=== Joining Proof for Compilation ===")
        print("\n".join(stored_tactics)) 
  

        print(f"🔹 Predicted Tactic: {predicted_tactic}")
        
        compilation_result = lean_compile("\n".join(stored_tactics), theorem_name)

        if compilation_result == "UNSOLVED_GOALS":
            print("✓ Tactic added, continuing with proof...")
        elif compilation_result:  # If Lean fails
            print(f"❌ Compilation Failed with error:")
            print(compilation_result)
            return len(proof_pairs), stored_tactics, compilation_result  

    print(f"\n=== Final Score ===")
    return len(proof_pairs), stored_tactics, None  

if __name__ == "__main__":
    "Clear existing stored tactics"
    globals()["stored_tactics"] = []
    #theorem_header = "theorem zero_add_test (n : MyNat) : 0 + n = n := by"
    theorem_header = "theorem add_comm_test (a b : ℕ) : a + b = b + a := by"
    matches, total = process_proof(lean_proof, "add_comm_test", theorem_header = "theorem add_comm_test (a b : ℕ) : a + b = b + a := by")
    
    
    
# from Model import gpt_prompt, parse_lean_proof, parse_nl_proof
# import sys
# import os
# from lean_compile import lean_compile
# # sys.path.append('/Users/manooshreepatel/dev/LeanTutor/backend/src')
# # from main import stored_tactics

# # Move to LeanTutor directory once at startup
# script_dir = os.path.dirname(os.path.abspath(__file__))
# os.chdir(os.path.join(script_dir, "../../../"))

# # Sample Lean proof
# lean_proof = '''
# -- Induct on n, with d = 0 as the base case and the inductive hypothesis 0 + d = d. There are now two proof goals, prove base case: 0 + 0 = 0, and inductive step: 0 + succ (d) = succ (d)
#   induction n with d hd
# -- First prove base case. Reduce LHS 0 + 0 = 0.
#   · rw [add_zero]
# -- Prove LHS and RHS are equal, 0 = 0, completing base case
#     rfl
# -- Now prove inductive step. Rewrite 0 + succ d = succ (0 + d)
#   · rw [add_succ]
# -- Simplify RHS succ (0 + d) = succ(d) using the inductive hypothesis.
#     rw [hd]
# -- Prove LHS and RHS are equal, succ(d) = succ(d), completing the proof
#     rfl
# '''


# # if "stored_tactics" not in globals():
# #     globals()["stored_tactics"] = [] 

# theorem_header = "theorem add_comm_test (a b : ℕ) : a + b = b + a := by"

# def process_proof(proof_lines, theorem_name, theorem_header):
#     if "stored_tactics" not in globals():
#         globals()["stored_tactics"] = []
#         if theorem_header:
#             globals()["stored_tactics"].append(theorem_header)

#     proof_pairs = parse_nl_proof(proof_lines)
#     print("Theorem header", theorem_header)
    
#     for i, (nl, _) in enumerate(proof_pairs):
#         print(f"\n🔹 Processing Step {i+1}/{len(proof_pairs)}\n")
#         print(f"NL: {nl}")

#         predicted_tactic = gpt_prompt(nl)
#         globals()["stored_tactics"].append(predicted_tactic)

#         print("\n=== Debugging Generated Tactics Before Compilation ===")
#         print(globals()["stored_tactics"])  
#         print("\n=== Joining Proof for Compilation ===")
#         print("\n".join(globals()["stored_tactics"]))

#         print(f"🔹 Predicted Tactic: {predicted_tactic}")
        
#         compilation_result = lean_compile("\n".join(globals()["stored_tactics"]), theorem_name)

#         if compilation_result == "UNSOLVED_GOALS":
#             print("✓ Tactic added, continuing with proof...")
#         elif compilation_result:  # If Lean fails
#             print(f"❌ Compilation Failed with error:")
#             print(compilation_result)
#             return len(proof_pairs), globals()["stored_tactics"], compilation_result  

#     print(f"\n=== Final Score ===")
#     return len(proof_pairs), globals()["stored_tactics"], compilation_result

# if __name__ == "__main__":
#     "Clear existing stored tactics"
#     globals()["stored_tactics"] = []
#     #theorem_header = "theorem zero_add_test (n : MyNat) : 0 + n = n := by"
#     theorem_header = "theorem add_comm_test (a b : ℕ) : a + b = b + a := by"
#     matches, total = process_proof(lean_proof, "add_comm_test", theorem_header = "theorem add_comm_test (a b : ℕ) : a + b = b + a := by")