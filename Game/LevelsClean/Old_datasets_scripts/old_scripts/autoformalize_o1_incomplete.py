import os
import json
from openai import OpenAI
from rag import lean_rag
from dotenv import load_dotenv
from lean_compile import lean_compile
import threading
import time
from NNG4.Game.LevelsClean.Scripts.dataset_scripts.parse_states import parse_unsolved_state, extract_intermediate_states

leanopeano_path = 'NNG4/Game/LevelsClean/Datasets/leanopeano_train_deviations.json'
tactic_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json'
theorem_path = 'NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json'
embed_path_examples = 'NNG4/Game/LevelsClean/Datasets/Embeddings/leanopeano_embeddings_deviations.pt'
embed_path_theorem = 'NNG4/Game/LevelsClean/Datasets/Embeddings/theorem_embeddings.pt'
embed_path_tactic = 'NNG4/Game/LevelsClean/Datasets/Embeddings/tactic_embeddings.pt'

load_dotenv("NNG4/.env")
client = OpenAI(api_key=os.environ.get("OPENAI_API_KEY"))

match_metric_num = 0
total_num_tactics = 0

def tuple_to_key(t):
    """Convert a tuple to a string key for JSON serialization"""
    return "|||".join(str(x) for x in t)

def key_to_tuple(s):
    """Convert a string key back to a tuple"""
    return tuple(s.split("|||"))

# Load saved outputs
tactic_outputs_lock = threading.Lock()
with open('NNG4/Game/LevelsClean/saved_outputs/gpt4_tactic_predictions_incomplete.json', 'r') as f:
    tactic_outputs_raw = json.load(f)
    tactic_outputs = {key_to_tuple(k): v for k, v in tactic_outputs_raw.items()}
goal_outputs_lock = threading.Lock()
with open('NNG4/Game/LevelsClean/saved_outputs/gpt4_goal_predictions_incomplete.json', 'r') as f:
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
            if g not in mappings:
                mappings[g] = p
            elif mappings[g] != p:
                return False
    return True

def get_goal_state(nl_statement: str, prev_goal: str, theorem_name: str):
    global goal_outputs
    global goal_outputs_lock

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
            with goal_outputs_lock:
                goal_outputs[(nl_statement, prev_goal)] = response.choices[0].message.content.strip()
        else:
            with goal_outputs_lock:
                goal_outputs[(nl_statement, prev_goal)] = "Ignore the predicted next state. Use the other information to predict the next step."
    return goal_outputs[(nl_statement, prev_goal)]

def get_formalized_line(nl_statement: str, 
                        prev_goal: str, 
                        theorem_name: str, 
                        predicted_next_state: str, 
                        theorem_dict: str, 
                        tactic_dict: str, 
                        whole_theorems: dict, 
                        lean_examples: str):
    
    global tactic_outputs
    global tactic_outputs_lock
    if (nl_statement, prev_goal, theorem_name, predicted_next_state) not in tactic_outputs:
        print("calling theorem", theorem_name)
        prompt = f"""
        We are proving {theorem_name}.
        This is one example of the proof of {theorem_name}:

        {whole_theorems[theorem_name]}

        Given a natural language mathematical statement, convert it to formal Lean theorem syntax.

        The natural language statement is:
        {nl_statement}

        The lean state has information about theorems or variables that have been introduced which might be used in the next step.
        The current state in lean is:
        {prev_goal}

        After applying the tactic, the state should be:
        {predicted_next_state}

        Here are some definitions of theorems and tactics to help you choose the correct example:
        {theorem_dict}
        {tactic_dict}

        These are some examples of lines of Lean code that are the formalized version of the natural language statement:
        {lean_examples}

        Give me only the line of Lean code that is the formalized version of the natural language statement.
        Do not include any other text or formatting.
        """
        while True:
            try:
                response = client.chat.completions.create(
                    model="gpt-4",
                    messages=[{"role": "user", "content": prompt}]
                )
                formalized = response.choices[0].message.content.strip()
                i = 0
                while i < 3 and len(formalized) > 30:
                # Get completion from GPT
                    response = client.chat.completions.create(
                        model="gpt-4",
                        messages=[{"role": "user", "content": prompt},
                                    {"role": "user", "content": "Output the best possible line of Lean code that you can find."}]
                    )
                    formalized = response.choices[0].message.content.strip()
                    i += 1
                break
            except Exception as e:
                print(f"Rate limit hit, sleeping for 40 seconds")
                time.sleep(40)
        with tactic_outputs_lock:
            tactic_outputs[(nl_statement, prev_goal, theorem_name, predicted_next_state)] = formalized
    return tactic_outputs[(nl_statement, prev_goal, theorem_name, predicted_next_state)]

def autoformalize(nl_statement: str, prev_goal: str, theorem_name: str):
    global theorem_dict, tactic_dict, whole_theorems

    predicted_next_state = get_goal_state(nl_statement, prev_goal, theorem_name)
    
    lean_examples = [i for i in whole_theorems[theorem_name].split("\n")[1:] if not i.startswith("--") and i]
    formalized = get_formalized_line(nl_statement, prev_goal, theorem_name, predicted_next_state, theorem_dict, tactic_dict, whole_theorems, lean_examples)
    
    return formalized

def autoformalize_threaded(theorem, items, results, results_lock, proof_results, proof_results_lock):
    print(f"Autoformalizing {theorem}")
    goal_state = ""
    proof_is_correct = True
    prev_fl = []
    for item in items:
        if item['FL'].startswith('theorem'):
            if prev_fl:
                with proof_results_lock:
                    proof_results.append({
                        'theorem': prev_fl[0].split()[1].strip('_temp'),
                        'proof_is_correct': proof_is_correct
                    })
                    print("theorem", prev_fl[0].split()[1].strip('_temp'), "proof_is_correct", proof_is_correct)
            prev_fl = [item['FL'].split()[0] + ' ' + item['FL'].split()[1] + '_temp' + ' ' + ' '.join(item['FL'].split()[2:])]
            proof_is_correct = True
            goal_state = item['state']
            continue
        nl = item['NL']
        expected_fl = item['FL']
        # autoformalize the next step
        predicted_fl = autoformalize(nl, goal_state, theorem)
        # add step so we can compile
        prev_fl.append(predicted_fl)
        # compile the proof
        compiler_output = lean_compile(theorem, prev_fl)
        # get the unsolved goal
        goal_state = parse_unsolved_state(compiler_output)
        if compiler_output.stdout and "unsolved goals" not in compiler_output.stdout:
            goal_state = "error"
        global total_num_tactics
        is_correct = predicted_fl == expected_fl or check_if_correct(item['state'], goal_state)
        total_num_tactics += 1
        if not is_correct:
            proof_is_correct = False
            # print("states didn't match\n", item['state'] + "\n" + goal_state, "\n predicted_fl", predicted_fl, "\n expected_fl", expected_fl)
        if not expected_fl.startswith('theorem'):
            with results_lock:
                results.append({
                    'NL': nl,  
                    'Expected': expected_fl,
                    'Predicted': predicted_fl,
                    'Correct': is_correct
                })

    with proof_results_lock:
        proof_results.append({
            'theorem': prev_fl[0],
            'proof_is_correct': proof_is_correct
        })

def evaluate_test_set(test_file: str):
    """Evaluate autoformalization on a test set"""
    with open(test_file, 'r') as f:
        test_data = json.load(f)

    results = []
    theorem_sections = {}
    current_theorem = ""
    for item in test_data:
        if not current_theorem or not item['theorem'].startswith(current_theorem):
            current_theorem = item['theorem']
            theorem_sections[current_theorem] = []
        theorem_sections[current_theorem].append(item)
    
    threads = []
    results = []
    results_lock = threading.Lock()
    proof_results = []
    proof_results_lock = threading.Lock()
    for theorem, items in theorem_sections.items():
        theorem = theorem.removeprefix("truncated_")
        thread = threading.Thread(target=autoformalize_threaded, args=(theorem, items, results, results_lock, proof_results, proof_results_lock))
        threads.append(thread)
        thread.start()
    for thread in threads:
        thread.join()

    # Calculate accuracy
    accuracy = f"{sum(r['Correct'] for r in results)} / {len(results)} = {sum(r['Correct'] for r in results) / len(results):.2%}"
    proof_accuracy = f"{sum(r['proof_is_correct'] for r in proof_results)} / {len(proof_results)} = {sum(r['proof_is_correct'] for r in proof_results) / len(proof_results):.2%}"

    return accuracy, proof_accuracy, proof_results

if __name__ == "__main__":
    # Example usage
    worlds = [
        'implication_world_val',
        'multiplication_world_val',
        'AdvMultiplication_world_val',
        'algorithm_world_val',
        'less_or_equal_world_val',
        'power_world_val',
        'tutorial_world_val',
        'AdvAddition_world_val',
        'addition_world_val'
    ]

    results_json = {}
    proof_results_json = {}
    for world in worlds:
        accuracy, proof_accuracy, proof_results = evaluate_test_set(f'NNG4/Game/LevelsClean/Datasets/world_vals_incomplete/{world}.json')
        results_json[world] = {
            'accuracy': accuracy,
            'proof_accuracy': proof_accuracy
        }
        proof_results_json[world] = proof_results
        # with open('NNG4/Game/LevelsClean/results/autoformalize_gpt4_incomplete.json', 'r') as f:
        #     existing_results = json.load(f)
        # existing_results.update(results_json)
        # with open('NNG4/Game/LevelsClean/results/autoformalize_gpt4_incomplete.json', 'w') as f:
        #     json.dump(existing_results, f)
        # with open('NNG4/Game/LevelsClean/saved_outputs/gpt4_tactic_predictions_incomplete.json', 'w') as f:
        #     tactic_outputs_serializable = {tuple_to_key(k): v for k, v in tactic_outputs.items()}
        #     json.dump(tactic_outputs_serializable, f)
        # with open('NNG4/Game/LevelsClean/saved_outputs/gpt4_goal_predictions_incomplete.json', 'w') as f:
        #     goal_outputs_serializable = {tuple_to_key(k): v for k, v in goal_outputs.items()}
        #     json.dump(goal_outputs_serializable, f)
        # print("len(tactic_outputs)", len(tactic_outputs))
        # print("len(goal_outputs)", len(goal_outputs))

        with open('NNG4/Game/LevelsClean/results/full_proof_results_incomplete.json', 'r') as f:
            full_proof_results = json.load(f)
        full_proof_results.update(proof_results_json)
        with open('NNG4/Game/LevelsClean/results/full_proof_results_incomplete.json', 'w') as f:
            json.dump(full_proof_results, f)
        
        print(f"Accuracy for {world}: {accuracy}")
        print(f"Proof Accuracy for {world}: {proof_accuracy}")
        print(f"Match metric frequency: {match_metric_num} / {total_num_tactics} = {match_metric_num / total_num_tactics}")
