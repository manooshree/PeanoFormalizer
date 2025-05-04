import os
import json
from openai import OpenAI
from rag import lean_rag
from dotenv import load_dotenv
from lean_compile import lean_compile
import time
from NNG4.Game.LevelsClean.Scripts.dataset_scripts.parse_states import parse_unsolved_state, extract_intermediate_states
import random

leanopeano_path = 'NNG4/Game/LevelsClean/Datasets/leanopeano_train_deviations.json'
tactic_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json'
theorem_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json'
embed_path_examples = 'NNG4/Game/LevelsClean/Datasets/Embeddings/leanopeano_embeddings_deviations.pt'
embed_path_theorem = 'NNG4/Game/LevelsClean/Datasets/Embeddings/theorem_embeddings.pt'
embed_path_tactic = 'NNG4/Game/LevelsClean/Datasets/Embeddings/tactic_embeddings.pt'

load_dotenv("NNG4/.env")
client = OpenAI(api_key="")

match_metric_num = 0
total_num_tactics = 0

def tuple_to_key(t):
    """Convert a tuple to a string key for JSON serialization"""
    return "|||".join(str(x) for x in t)

def key_to_tuple(s):
    """Convert a string key back to a tuple"""
    return tuple(s.split("|||"))

# Load saved outputs
with open('NNG4/Game/LevelsClean/saved_outputs/gpt4_tactic_predictions.json', 'r') as f:
    tactic_outputs_raw = json.load(f)
    tactic_outputs = {key_to_tuple(k): v for k, v in tactic_outputs_raw.items()}
with open('NNG4/Game/LevelsClean/saved_outputs/ablations/gpt4_goal_predictions_no_next_state.json', 'r') as f:
    goal_outputs_raw = json.load(f)
    goal_outputs = {key_to_tuple(k): v for k, v in goal_outputs_raw.items()}

# Load theorem and tactic dictionaries
with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json', 'r') as f:
    theorem_dict = json.load(f)
with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json', 'r') as f:
    tactic_dict = json.load(f)
with open('NNG4/Game/LevelsClean/Datasets/whole_proofs.json', 'r') as f:
    whole_theorems = json.load(f)

def check_if_correct(ground_truth: str, predicted: str):
    global match_metric_num
    match_metric_num += 1
    ground_truth = ground_truth.strip("\n")
    predicted = predicted.strip("\n")
    if ground_truth == predicted:
        return True
    if len(ground_truth.split()) != len(predicted.split()):
        return False
    mappings = {}
    for i, (g, p) in enumerate(zip(ground_truth.split(), predicted.split())):
        if g != p:
            print(mappings)
            if g not in mappings:
                mappings[g] = p
            elif mappings[g] != p:
                print(g, p, mappings[g])
                return False
    return True

def get_goal_state(nl_statement: str, prev_goal: str, theorem_name: str):
    global goal_outputs

    if (nl_statement, prev_goal) not in goal_outputs:
        prompt_predict_next_state = f"""
        Here is the current proof state:
        {prev_goal}
        
        I need to predict what the state will be after applying this step:
        "{nl_statement}"
        
        INSTRUCTIONS:
        1. Analyze the current state and the natural language description
        2. Predict what the mathematical expression will look like after this step
        3. Output ONLY the predicted state with no additional text or explanation
        4. Make sure to include brackets when necessary
        """
        if prev_goal != "error":
            while True:
                try:
                    response = client.chat.completions.create(
                        model="gpt-4",
                        messages=[{"role": "user", "content": prompt_predict_next_state}]
                    )
                    break
                except Exception as e:
                    print(f"Rate limit hit, sleeping for 40 seconds")
                    time.sleep(40)
            goal_outputs[(nl_statement, prev_goal)] = response.choices[0].message.content.strip()
        else:
            goal_outputs[(nl_statement, prev_goal)] = "Ignore the predicted next state. Use the other information to predict the next step."
    return goal_outputs[(nl_statement, prev_goal)]

def get_formalized_line(nl_statement: str, 
                        prev_goal: str, 
                        theorem_name: str, 
                        predicted_next_state: str, 
                        theorem_dict: str, 
                        tactic_dict: str, 
                        whole_theorems: dict, 
                        lean_examples: str,
                        prev_fl: list):
    global tactic_outputs
    if (nl_statement, prev_goal, theorem_name, predicted_next_state) not in tactic_outputs or True: 
        print("calling theorem", theorem_name)
        system_prompt = """Convert proofs written in Natural Language by students into Lean4 code

The name of the theorem we are working with is {}.
This is the theorem statement in natural language: {}
This is the theorem statement in formal language: {}     

This is one example of the proof of {} with alternating natural language and formal language steps (each formal line of lean conde directly follows its corresponding natural language line of lean code):

{}

Your proofs can make use of the following construction rules and inference rules:
{}

Your response must be a tactic proof in the Natural Numbers Game 4 DSL. This DSL is built from the following tactics (arguments indicated by "name_of_theorem" ):
{}
You're response must be written as a single line of Lean tactic code, as used in the body of a by block of a Lean theorem. It should match the structure of Lean DSL tactic proofs, such as:
intro h 
rw [← is_zero_succ a]
apply succ_inj at h
exact h
contrapose! h

Note: Only 1 lean tactic, do not write multiple lean tactics that are comma seperated.

Each line must correspond to a valid Lean tactic (e.g. intro, rw, apply, exact, trivial, etc.), optionally with arguments in parentheses or brackets, and formatted consistently with Lean4's syntax.

DO *NOT* wrap your answer in markdown syntax, e.g. '''lean '''. It must be simply a Lean tactic script that can be inserted into a proof.

Here are some examples. NOTE: These are just examples. The correct Lean4 code may not necessarily use the propositions shown in these proofs.

Example 1:
Input: -- Rewrite the LHS pred (succ a) with the given statement that succ a = succ b, LHS is now pred (succ b)
Output: rw [h]

Example 2:
Input: -- Simplify the LHS 0 * d + 0 to 0 + 0 using the inductive hypothesis
Output: rw [hd]

Example 3: 
Input: -- Assume that the hypothesis 'h' is true, that is, a + succ d = 0. The goal now is to prove that a = 0.
Output: rw [add_zero] at h

Example 4:
Input:  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
Output: rw [pow_zero]

Example 5:
Input: -- Use the case of a + b to simplify the goal to equal z = x + (a + b).
Output: use a + b
""".format(
    theorem_name,
    whole_theorems[theorem_name].split("\n")[0],
    whole_theorems[theorem_name].split("\n")[1],
    theorem_name,
    whole_theorems[theorem_name],
    theorem_dict,
    tactic_dict
)

        prompt = f'''{nl_statement}'''

        prompt_error = lambda compiler_error : f'''
            The line of Lean code you provided did not compile.
            Error message: {compiler_error}

            Please revise your output to fix this error.
            Remember to formalize this natural language statement: {nl_statement}

            Provide ONLY the corrected line of Lean code with no additional text or formatting.
        '''

        try:
            messages = [
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": prompt}]
            
            response = client.chat.completions.create(
                model="gpt-4",
                messages=messages
            )
            formalized = response.choices[0].message.content.strip()
            proof_to_compiler = prev_fl + [formalized]
            compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
            i = 3
            print(theorem_name, compiler_output.stdout)
            while compiler_output.stdout and "unsolved goals" not in compiler_output.stdout:
                print("ENTERED")
                # print(theorem_name, compiler_output.stdout)
                messages.append({"role": "assistant", "content": formalized})
                messages.append({"role": "user", "content": prompt_error(compiler_output.stdout)})
                response = client.chat.completions.create(
                    model="gpt-4",
                    messages=messages
                )   
                formalized = response.choices[0].message.content.strip() 
                proof_to_compiler = prev_fl + [formalized]
                compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
                if i <= 0:
                    print("FAILED")
                    break
                i -= 1
        except Exception as e:
            print(f"Rate limit hit, sleeping for 40 seconds")
            time.sleep(40)
        tactic_outputs[(nl_statement, prev_goal, theorem_name, predicted_next_state)] = formalized
    return tactic_outputs[(nl_statement, prev_goal, theorem_name, predicted_next_state)]

def autoformalize(nl_statement: str, prev_goal: str, theorem_name: str, prev_fl: list):
    global theorem_dict, tactic_dict, whole_theorems
    
    lean_examples = [i for i in whole_theorems[theorem_name].split("\n")[1:] if not i.startswith("--") and i]
    formalized = get_formalized_line(nl_statement, prev_goal, theorem_name, "", theorem_dict, tactic_dict, whole_theorems, lean_examples, prev_fl)
    
    return formalized

def autoformalize_threaded(theorem, proofs, results, proof_results):
    print(f"Autoformalizing {theorem}")
    goal_state = ""
    proof_is_correct = True
    prev_fl = []
    for proof_dev, proof in proofs.items():
        prev_fl = [proof[0]['FL'].split()[0] + ' ' + proof[0]['FL'].split()[1] + '_temp' + ' ' + ' '.join(proof[0]['FL'].split()[2:])]
        proof_is_correct = True
        goal_state = proof[0]['state']
        for step in proof[1:]:
            # autoformalize the next step
            predicted_fl = autoformalize(step['NL'], goal_state, theorem, prev_fl)
            # add step so we can compile
            prev_fl.append(predicted_fl)
            # compile the proof
            compiler_output = lean_compile(proof_dev, prev_fl)
            # get the unsolved goal
            goal_state = parse_unsolved_state(compiler_output)
            if compiler_output.stdout and "unsolved goals" not in compiler_output.stdout:
                goal_state = "error"
            global total_num_tactics
            is_correct = predicted_fl == step['FL'] or check_if_correct(step['state'], goal_state)
            total_num_tactics += 1
            if not is_correct:
                proof_is_correct = False
            results.append({
                'NL': step['NL'],  
                'Expected': step['FL'],
                'Predicted': predicted_fl,
                'Correct': is_correct
            })
        proof_results.append({
            'theorem': prev_fl[0].split()[1].strip('_temp'),
            'proof_is_correct': proof_is_correct
        })
        print("theorem", prev_fl[0].split()[1].strip('_temp'), "proof_is_correct", proof_is_correct)

def evaluate_test_set(test_file: str, theorem_name: str):
    """Evaluate autoformalization on a test set"""
    with open(test_file, 'r') as f:
        test_data = json.load(f)
    
    results = []
    proof_results = []
    random.seed(42)
    if theorem_name:
        theorem = theorem_name
        proofs = test_data[theorem_name]
    else:
        theorem, proofs = list(test_data.items())[random.randint(0, len(test_data) - 1)]
    autoformalize_threaded(theorem, proofs, results, proof_results)

    # Calculate accuracy
    accuracy = f"Accuracy: {sum(r['Correct'] for r in results)} / {len(results)} = {sum(r['Correct'] for r in results) / len(results):.2%}"
    proof_accuracy = f"Proof Accuracy: {sum(r['proof_is_correct'] for r in proof_results)} / {len(proof_results)} = {sum(r['proof_is_correct'] for r in proof_results) / len(proof_results):.2%}"

    return accuracy, proof_accuracy

# def evaluate_test_set(test_file: str):
#     """Evaluate autoformalization on a test set"""
#     with open(test_file, 'r') as f:
#         test_data = json.load(f)
    
#     results = []
#     proof_results = []
    
#     for theorem, proofs in test_data.items():
#         if len(proofs) > 0:
#             print(f"Autoformalizing {theorem}")
#             goal_state = ""
#             proof_is_correct = True
#             prev_fl = []
#             for proof_dev, proof in proofs.items():
#                 prev_fl = [proof[0]['FL'].split()[0] + ' ' + proof[0]['FL'].split()[1] + '_temp' + ' ' + ' '.join(proof[0]['FL'].split()[2:])]
#                 proof_is_correct = True
#                 goal_state = proof[0]['state']
#                 for step in proof[1:]:
#                     # autoformalize the next step
#                     predicted_fl = autoformalize(step['NL'], goal_state, theorem, prev_fl)
#                     # add step so we can compile
#                     prev_fl.append(predicted_fl)
#                     # compile the proof
#                     compiler_output = lean_compile(proof_dev, prev_fl)
#                     # get the unsolved goal
#                     goal_state = parse_unsolved_state(compiler_output)
#                     if compiler_output.stdout and "unsolved goals" not in compiler_output.stdout:
#                         goal_state = "error"
#                     global total_num_tactics
#                     is_correct = predicted_fl == step['FL'] or check_if_correct(step['state'], goal_state)
#                     total_num_tactics += 1
#                     if not is_correct:
#                         proof_is_correct = False
#                     results.append({
#                         'NL': step['NL'],  
#                         'Expected': step['FL'],
#                         'Predicted': predicted_fl,
#                         'Correct': is_correct
#                     })
#                 proof_results.append({
#                     'theorem': prev_fl[0].split()[1].strip('_temp'),
#                     'proof_is_correct': proof_is_correct
#                 })
#                 print("theorem", prev_fl[0].split()[1].strip('_temp'), "proof_is_correct", proof_is_correct)
#         else:
#             print("no items for theorem", theorem)

#     # Calculate accuracy
#     accuracy = f"Accuracy: {sum(r['Correct'] for r in results)} / {len(results)} = {sum(r['Correct'] for r in results) / len(results):.2%}"
#     proof_accuracy = f"Proof Accuracy: {sum(r['proof_is_correct'] for r in proof_results)} / {len(proof_results)} = {sum(r['proof_is_correct'] for r in proof_results) / len(proof_results):.2%}"

#     return accuracy, proof_accuracy

if __name__ == "__main__":
    # Example usage
    worlds = [
        ('implication_world_val', 'exact_2'),
        ('multiplication_world_val', ''),
        ('AdvMultiplication_world_val', ''),
        ('algorithm_world_val', 'add_left_comm'),
        ('less_or_equal_world_val', ''),
        ('power_world_val', ''),
        ('tutorial_world_val', ''),
        ('AdvAddition_world_val', 'add_right_eq_zero'),
        ('addition_world_val', '')
    ]

    results_json = {}
    for world in worlds:
        accuracy, proof_accuracy = evaluate_test_set(f'NNG4/Game/LevelsClean/Datasets/full_clean_dataset/correct_json/{world[0]}.json', world[1])
        results_json[world[0]] = {
            'accuracy': accuracy,
            'proof_accuracy': proof_accuracy
        }
        with open('NNG4/Game/LevelsClean/results/autoformalize_gpt4.json', 'r') as f:
            existing_results = json.load(f)
        existing_results.update(results_json)
        with open('NNG4/Game/LevelsClean/results/autoformalize_gpt4.json', 'w') as f:
            json.dump(existing_results, f)
        with open('NNG4/Game/LevelsClean/saved_outputs/gpt4_tactic_predictions.json', 'w') as f:
            tactic_outputs_serializable = {tuple_to_key(k): v for k, v in tactic_outputs.items()}
            json.dump(tactic_outputs_serializable, f)
        with open('NNG4/Game/LevelsClean/saved_outputs/ablations/gpt4_goal_predictions_no_next_state.json', 'w') as f:
            goal_outputs_serializable = {tuple_to_key(k): v for k, v in goal_outputs.items()}
            json.dump(goal_outputs_serializable, f)
        print("len(tactic_outputs)", len(tactic_outputs))
        print("len(goal_outputs)", len(goal_outputs))
        
        print(f"Accuracy for {world}: {accuracy}")
        print(f"Proof Accuracy for {world}: {proof_accuracy}")
        print(f"Match metric frequency: {match_metric_num} / {total_num_tactics} = {match_metric_num / total_num_tactics}")
# import os
# import json
# from openai import OpenAI
# from rag import lean_rag
# from dotenv import load_dotenv
# from lean_compile import lean_compile
# import threading
# import time
# from parse_states import parse_unsolved_state, extract_intermediate_states

# leanopeano_path = 'NNG4/Game/LevelsClean/Datasets/leanopeano_train_deviations.json'
# tactic_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json'
# theorem_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json'
# embed_path_examples = 'NNG4/Game/LevelsClean/Datasets/Embeddings/leanopeano_embeddings_deviations.pt'
# embed_path_theorem = 'NNG4/Game/LevelsClean/Datasets/Embeddings/theorem_embeddings.pt'
# embed_path_tactic = 'NNG4/Game/LevelsClean/Datasets/Embeddings/tactic_embeddings.pt'

# load_dotenv("NNG4/.env")
# client = OpenAI(api_key="")

# match_metric_num = 0
# total_num_tactics = 0

# def tuple_to_key(t):
#     """Convert a tuple to a string key for JSON serialization"""
#     return "|||".join(str(x) for x in t)

# def key_to_tuple(s):
#     """Convert a string key back to a tuple"""
#     return tuple(s.split("|||"))

# # Load saved outputs
# tactic_outputs_lock = threading.Lock()
# with open('NNG4/Game/LevelsClean/saved_outputs/gpt4_tactic_predictions.json', 'r') as f:
#     tactic_outputs_raw = json.load(f)
#     tactic_outputs = {key_to_tuple(k): v for k, v in tactic_outputs_raw.items()}
# goal_outputs_lock = threading.Lock()
# with open('NNG4/Game/LevelsClean/saved_outputs/ablations/gpt4_goal_predictions_no_next_state.json', 'r') as f:
#     goal_outputs_raw = json.load(f)
#     goal_outputs = {key_to_tuple(k): v for k, v in goal_outputs_raw.items()}

# # Load theorem and tactic dictionaries
# with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json', 'r') as f:
#     theorem_dict = json.load(f)
# with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json', 'r') as f:
#     tactic_dict = json.load(f)
# with open('NNG4/Game/LevelsClean/Datasets/whole_proofs.json', 'r') as f:
#     whole_theorems = json.load(f)

# def check_if_correct(ground_truth: str, predicted: str):
#     global match_metric_num
#     match_metric_num += 1
#     ground_truth = ground_truth.strip("\n")
#     predicted = predicted.strip("\n")
#     if ground_truth == predicted:
#         return True
#     if len(ground_truth.split()) != len(predicted.split()):
#         return False
#     mappings = {}
#     for i, (g, p) in enumerate(zip(ground_truth.split(), predicted.split())):
#         if g != p:
#             print(mappings)
#             if g not in mappings:
#                 mappings[g] = p
#             elif mappings[g] != p:
#                 print(g, p, mappings[g])
#                 return False
#     return True

# def get_goal_state(nl_statement: str, prev_goal: str, theorem_name: str):
#     global goal_outputs
#     global goal_outputs_lock

#     if (nl_statement, prev_goal) not in goal_outputs:
#         prompt_predict_next_state = f"""
#         Here is the current proof state:
#         {prev_goal}
        
#         I need to predict what the state will be after applying this step:
#         "{nl_statement}"
        
#         INSTRUCTIONS:
#         1. Analyze the current state and the natural language description
#         2. Predict what the mathematical expression will look like after this step
#         3. Output ONLY the predicted state with no additional text or explanation
#         4. Make sure to include brackets when necessary
#         """
#         if prev_goal != "error":
#             while True:
#                 try:
#                     response = client.chat.completions.create(
#                         model="gpt-4",
#                         messages=[{"role": "user", "content": prompt_predict_next_state}]
#                     )
#                     break
#                 except Exception as e:
#                     print(f"Rate limit hit, sleeping for 40 seconds")
#                     time.sleep(40)
#             with goal_outputs_lock:
#                 goal_outputs[(nl_statement, prev_goal)] = response.choices[0].message.content.strip()
#         else:
#             with goal_outputs_lock:
#                 goal_outputs[(nl_statement, prev_goal)] = "Ignore the predicted next state. Use the other information to predict the next step."
#     return goal_outputs[(nl_statement, prev_goal)]

# def get_formalized_line(nl_statement: str, 
#                         prev_goal: str, 
#                         theorem_name: str, 
#                         predicted_next_state: str, 
#                         theorem_dict: str, 
#                         tactic_dict: str, 
#                         whole_theorems: dict, 
#                         lean_examples: str,
#                         prev_fl: list):
#     global tactic_outputs
#     global tactic_outputs_lock
#     if (nl_statement, prev_goal, theorem_name, predicted_next_state) not in tactic_outputs or True: 
#         print("calling theorem", theorem_name)
#         system_prompt = system_prompt = """Convert proofs written in Natural Language by students into Lean4 code

# The name of the theorem we are working with is {}.
# This is the theorem statement in natural language: {}
# This is the theorem statement in formal language: {}     

# This is one example of the proof of {} with alternating natural language and formal language steps (each formal line of lean conde directly follows its corresponding natural language line of lean code):

# {}

# Your proofs can make use of the following construction rules and inference rules:
# {}

# Your response must be a tactic proof in the Natural Numbers Game 4 DSL. This DSL is built from the following tactics (arguments indicated by "name_of_theorem" ):
# {}
# You're response must be written as a single line of Lean tactic code, as used in the body of a by block of a Lean theorem. It should match the structure of Lean DSL tactic proofs, such as:
# intro h 
# rw [← is_zero_succ a]
# apply succ_inj at h
# exact h
# contrapose! h

# Each line must correspond to a valid Lean tactic (e.g. intro, rw, apply, exact, trivial, etc.), optionally with arguments in parentheses or brackets, and formatted consistently with Lean4's syntax.

# DO *NOT* wrap your answer in markdown syntax, e.g. '''lean '''. It must be simply a Lean tactic script that can be inserted into a proof.

# Here are some examples. NOTE: These are just examples. The correct Lean4 code may not necessarily use the propositions shown in these proofs.

# Example 1:
# Input: -- Rewrite the LHS pred (succ a) with the given statement that succ a = succ b, LHS is now pred (succ b)
# Output: rw [h]

# Example 2:
# Input: -- Simplify the LHS 0 * d + 0 to 0 + 0 using the inductive hypothesis
# Output: rw [hd]

# Example 3: 
# Input: -- Assume that the hypothesis 'h' is true, that is, a + succ d = 0. The goal now is to prove that a = 0.
# Output: rw [add_zero] at h

# Example 4:
# Input:  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
# Output: rw [pow_zero]

# Example 5:
# Input: -- Use the case of a + b to simplify the goal to equal z = x + (a + b).
# Output: use a + b
# """.format(
#     theorem_name,
#     whole_theorems[theorem_name].split("\n")[0],
#     whole_theorems[theorem_name].split("\n")[1],
#     theorem_name,
#     whole_theorems[theorem_name],
#     theorem_dict,
#     tactic_dict
# )

#         prompt = f'''{nl_statement}'''

#         prompt_error = lambda compiler_error : f'''
#             The line of Lean code you provided did not compile.
#             Error message: {compiler_error}

#             Please revise your output to fix this error.
#             Remember to formalize this natural language statement: {nl_statement}

#             Provide ONLY the corrected line of Lean code with no additional text or formatting.
#         '''


#         try:
#             messages = [
#                     {"role": "system", "content": system_prompt},
#                     {"role": "user", "content": prompt}]
            
#             response = client.chat.completions.create(
#                 model="gpt-4",
#                 messages= messages
#             )
#             formalized = response.choices[0].message.content.strip()
#             proof_to_compiler = prev_fl + [formalized]
#             compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
#             i = 3
#             print(theorem_name, compiler_output.stdout)
#             while compiler_output.stdout and "unsolved goals" not in compiler_output.stdout:
#                 print("ENTERED")
#                 # print(theorem_name, compiler_output.stdout)
#                 messages.append({"role": "user", "content": prompt_error(compiler_output.stdout)})
#                 response = client.chat.completions.create(
#                 model="gpt-4",
#                 messages= messages
#                 )   
#                 formalized = response.choices[0].message.content.strip() 
#                 if i <= 0:
#                     print("FAILED")
#                     break
#                 i -= 1

#                 # i = 0
#                 # while i < 3 and len(formalized) > 30:
#                 # # Get completion from GPT
#                 #     response = client.chat.completions.create(
#                 #         model="gpt-4",
#                 #         messages=[
#                 #         {"role": "system", "content": system_prompt},
#                 #         {"role": "user", "content": prompt}]
                                    
                                
#                 #     )
#                 #     formalized = response.choices[0].message.content.strip()
#                 #     i += 1
#                 # break
#         except Exception as e:
#             print(f"Rate limit hit, sleeping for 40 seconds")
#             time.sleep(40)
#         with tactic_outputs_lock:
#             tactic_outputs[(nl_statement, prev_goal, theorem_name, predicted_next_state)] = formalized
#     return tactic_outputs[(nl_statement, prev_goal, theorem_name, predicted_next_state)]

# def autoformalize(nl_statement: str, prev_goal: str, theorem_name: str, prev_fl: list):
#     global theorem_dict, tactic_dict, whole_theorems

#     # predicted_next_state = get_goal_state(nl_statement, prev_goal, theorem_name)
    
#     lean_examples = [i for i in whole_theorems[theorem_name].split("\n")[1:] if not i.startswith("--") and i]
#     formalized = get_formalized_line(nl_statement, prev_goal, theorem_name, "", theorem_dict, tactic_dict, whole_theorems, lean_examples, prev_fl)
    
#     return formalized

# def autoformalize_threaded(theorem, proofs, results, results_lock, proof_results, proof_results_lock):
#     print(f"Autoformalizing {theorem}")
#     goal_state = ""
#     proof_is_correct = True
#     prev_fl = []
#     for proof_dev, proof in proofs.items():
#         prev_fl = [proof[0]['FL'].split()[0] + ' ' + proof[0]['FL'].split()[1] + '_temp' + ' ' + ' '.join(proof[0]['FL'].split()[2:])]
#         proof_is_correct = True
#         goal_state = proof[0]['state']
#         for step in proof[1:]:
#             # autoformalize the next step
#             predicted_fl = autoformalize(step['NL'], goal_state, theorem, prev_fl)
#             # add step so we can compile
#             prev_fl.append(predicted_fl)
#             # compile the proof
#             compiler_output = lean_compile(proof_dev, prev_fl)
#             # get the unsolved goal
#             goal_state = parse_unsolved_state(compiler_output)
#             if compiler_output.stdout and "unsolved goals" not in compiler_output.stdout:
#                 goal_state = "error"
#             global total_num_tactics
#             is_correct = predicted_fl == step['FL'] or check_if_correct(step['state'], goal_state)
#             total_num_tactics += 1
#             if not is_correct:
#                 proof_is_correct = False
#             with results_lock:
#                 results.append({
#                     'NL': step['NL'],  
#                     'Expected': step['FL'],
#                     'Predicted': predicted_fl,
#                     'Correct': is_correct
#                 })
#         with proof_results_lock:
#             proof_results.append({
#                 'theorem': prev_fl[0].split()[1].strip('_temp'),
#                 'proof_is_correct': proof_is_correct
#             })
#         print("theorem", prev_fl[0].split()[1].strip('_temp'), "proof_is_correct", proof_is_correct)

# def evaluate_test_set(test_file: str):
#     """Evaluate autoformalization on a test set"""
#     with open(test_file, 'r') as f:
#         test_data = json.load(f)
    
#     threads = []
#     results = []
#     results_lock = threading.Lock()
#     proof_results = []
#     proof_results_lock = threading.Lock()
#     for theorem, proofs in test_data.items():
#         if len(proofs) > 0:
#             thread = threading.Thread(target=autoformalize_threaded, args=(theorem, proofs, results, results_lock, proof_results, proof_results_lock))
#             threads.append(thread)
#             thread.start()
#         else:
#             print("no items for theorem", theorem)
#     for thread in threads:
#         thread.join()

#     # Calculate accuracy
#     accuracy = f"Accuracy: {sum(r['Correct'] for r in results)} / {len(results)} = {sum(r['Correct'] for r in results) / len(results):.2%}"
#     proof_accuracy = f"Proof Accuracy: {sum(r['proof_is_correct'] for r in proof_results)} / {len(proof_results)} = {sum(r['proof_is_correct'] for r in proof_results) / len(proof_results):.2%}"

#     return accuracy, proof_accuracy

# if __name__ == "__main__":
#     # Example usage
#     worlds = [
#         # 'implication_world_val',
#         # 'multiplication_world_val',
#         # 'AdvMultiplication_world_val',
#         # 'algorithm_world_val',
#         # 'less_or_equal_world_val',
#         'power_world_val',
#         # 'tutorial_world_val',
#         # 'AdvAddition_world_val',
#         # 'addition_world_val'
#     ]

#     results_json = {}
#     for world in worlds:
#         accuracy, proof_accuracy = evaluate_test_set(f'NNG4/Game/LevelsClean/Datasets/full_clean_dataset/correct_json/{world}.json')
#         results_json[world] = {
#             'accuracy': accuracy,
#             'proof_accuracy': proof_accuracy
#         }
#         with open('NNG4/Game/LevelsClean/results/autoformalize_gpt4.json', 'r') as f:
#             existing_results = json.load(f)
#         existing_results.update(results_json)
#         with open('NNG4/Game/LevelsClean/results/autoformalize_gpt4.json', 'w') as f:
#             json.dump(existing_results, f)
#         with open('NNG4/Game/LevelsClean/saved_outputs/gpt4_tactic_predictions.json', 'w') as f:
#             tactic_outputs_serializable = {tuple_to_key(k): v for k, v in tactic_outputs.items()}
#             json.dump(tactic_outputs_serializable, f)
#         with open('NNG4/Game/LevelsClean/saved_outputs/ablations/gpt4_goal_predictions_no_next_state.json', 'w') as f:
#             goal_outputs_serializable = {tuple_to_key(k): v for k, v in goal_outputs.items()}
#             json.dump(goal_outputs_serializable, f)
#         print("len(tactic_outputs)", len(tactic_outputs))
#         print("len(goal_outputs)", len(goal_outputs))
        
#         print(f"Accuracy for {world}: {accuracy}")
#         print(f"Proof Accuracy for {world}: {proof_accuracy}")
#         print(f"Match metric frequency: {match_metric_num} / {total_num_tactics} = {match_metric_num / total_num_tactics}")
