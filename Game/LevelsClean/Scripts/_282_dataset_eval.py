import os
import json
import sys
import argparse
from dataset_scripts.parse_states import parse_unsolved_state, extract_intermediate_states
import csv
from _282_evaluate import calculate_accuracy, evaluate_proof
from helper_scripts.save_results import save_full_results
from _282_autoformalizer import autoformalize_deepseek
from helper_scripts.lean_compile import lean_compile

sys.path.append('../')

WORLDS = [
    # ('implication_world_val', 'exact_2'),
    # ('multiplication_world_val', 'zero_mul'),
    # ('AdvMultiplication_world_val', 'mul_left_ne_zero'),
    # ('algorithm_world_val', 'add_left_comm'), 
    # ('less_or_equal_world_val', 'le_two'),
    # ('power_world_val', 'zero_pow_succ'),
    # ('tutorial_world_val', 'succ_eq_add_one'),
    # ('AdvAddition_world_val', 'add_right_eq_zero'),
    ('addition_world_val', 0)
]

TEST_FILES = [
    "correct_test.json"
    # "correct_train.json", 
    # "correct_val.json"
]

parser = argparse.ArgumentParser(description='Evaluate proofs')

CORRECT = True


proof_type = "correct" 

# Create cache directory if does not exist
GPT_CACHE_DIR = 'Game/LevelsClean/saving_outputs/GPT_cache'
os.makedirs(GPT_CACHE_DIR, exist_ok=True)

EXPERIMENT_NAME = "deepseek_sft_3" # TODO CHANGE ALWAYS

# Add directory for list of LLM outputs and expected outputs as a csv
GPT_OUTPUTS_DIR = f'Game/LevelsClean/saving_outputs/GPT_outputs/{EXPERIMENT_NAME}_{proof_type}'

# consolidated metrics
os.makedirs(GPT_OUTPUTS_DIR, exist_ok=True)
RESULTS_FILE = f'Game/LevelsClean/saving_outputs/Results/{EXPERIMENT_NAME}_{proof_type}.csv'

# Path for consolidated CSV file of LLM outputs and expected outputs
CONSOLIDATED_CSV_FILE = os.path.join(GPT_OUTPUTS_DIR, 'all_results.csv')
# Check if consolidated file exists
CONSOLIDATED_CSV_EXISTS = os.path.exists(CONSOLIDATED_CSV_FILE)

TEST_DATA_DIR = f'Game/LevelsClean/Datasets/full_clean_dataset/_282_correct_json' 

SAME_TAC_FILE = f'Game/LevelsClean/metric_cases/same_tac_diff_goal.csv'
SAME_GOAL_FILE = f'Game/LevelsClean/metric_cases/diff_tac_same_goal.csv'

def get_all_theorems_from_file(file_path: str):
    with open(file_path, 'r') as f:
        test_data = json.load(f)
    return list(test_data.keys())


def autoformalize_threaded(theorem, items):
    print(f"Autoformalizing {theorem}")
    goal_state = ""
    prev_fl = []
        
    autoformalized_output = {}
    for proof_dev, proof in items.items():
        theorem_declaration = proof[0]['FL'].split()[0] + ' ' + proof[0]['FL'].split()[1] + '_temp' + ' ' + ' '.join(proof[0]['FL'].split()[2:])
        goal_state = proof[0]['state']    
        prev_nl = []
        # Collect all NL steps first
        all_nl_steps = [step['NL'] for step in proof[1:]]
        all_predicted_fl = [theorem_declaration]
        true_fl = [step['FL'] for step in proof[1:]]
        for step in proof[1:]:
            compiler_output = lean_compile(theorem_declaration, [theorem_declaration] + prev_fl)
            current_lean_state = parse_unsolved_state(compiler_output)

            # DeepSeek autoformalizer 
            predicted_fl = autoformalize_deepseek(step['NL'], current_lean_state, theorem_declaration)
            all_predicted_fl.append(predicted_fl)
            prev_nl.append(step['NL'])
        autoformalized_output[proof_dev] = all_predicted_fl
    return autoformalized_output


def get_world_results(file_path: str, theorem_name: str, world_name: str):
    with open(file_path, 'r') as f:
        test_data = json.load(f)

    results = []
    proof_results = []
    theorem = theorem_name
    proofs = test_data[theorem_name]

    num_succ_proofs = 0
    num_succ_tactics = 0
    autoformalized_output = autoformalize_threaded(theorem, proofs)
    for predicted_proof, ground_truth_proof in zip(autoformalized_output.values(), list(proofs.values())):
        true_fl = [step['FL'] for step in ground_truth_proof[1:]]
        nl_steps = [step['NL'] for step in ground_truth_proof[1:]]
        theorem_declaration = ground_truth_proof[0]['FL'].split()[0] + ' ' + ground_truth_proof[0]['FL'].split()[1] + '_temp' + ' ' + ' '.join(ground_truth_proof[0]['FL'].split()[2:])
        steps_are_correct = []
        
        print("theorem_declaration", theorem_declaration)
        res, tactic_accuracy, proof_is_correct, num_successful = evaluate_proof(predicted_proof[1:], true_fl, theorem_declaration, steps_are_correct)
        
        results.extend(res)
        proof_results.append({
            'theorem': theorem_declaration,
            'proof_is_correct': proof_is_correct
        })
        num_succ_tactics += num_successful
        num_succ_proofs += int(proof_is_correct)
    
        save_full_results(res, nl_steps, GPT_OUTPUTS_DIR, theorem_name, CONSOLIDATED_CSV_FILE, CORRECT)

    print("num_succ_tactics", num_succ_tactics, "num_succ_proofs", num_succ_proofs, "len_results", len(results), "len_proof_results", len(proof_results))
    return num_succ_tactics, num_succ_proofs, len(results), len(proof_results)
    

def evaluate_test_set():
    """Evaluate autoformalization on a test set"""

    if not os.path.exists(RESULTS_FILE):
        with open(RESULTS_FILE, 'w') as f:
            csv_writer = csv.writer(f)
            csv_writer.writerow(["World Name", "Theorem Name", "Correct Accuracy", "Proof Accuracy"])

    total_succ_tactics = 0
    total_succ_proofs = 0
    total_tactics = 0
    total_proofs = 0

    for filename in TEST_FILES:
        file_path = os.path.join(TEST_DATA_DIR, filename)
        with open(file_path, 'r') as f:
            test_data = json.load(f)

        for theorem_name in test_data:
            num_succ_tactics, num_succ_proofs, len_tactics, len_proofs = get_world_results(
                file_path,
                theorem_name,
                filename  # using filename as world identifier
            )

            total_succ_tactics += num_succ_tactics
            total_succ_proofs += num_succ_proofs
            total_tactics += len_tactics
            total_proofs += len_proofs

            # Handle division by zero for correct accuracy
            tactics_accuracy = calculate_accuracy(num_succ_tactics, len_tactics)
            proofs_accuracy = calculate_accuracy(num_succ_proofs, len_proofs)
            
            with open(RESULTS_FILE, 'a') as f:
                csv_writer = csv.writer(f)
                csv_writer.writerow([filename, theorem_name, tactics_accuracy, proofs_accuracy])

            print(f"Tactics Accuracy for {filename} → {theorem_name}: {tactics_accuracy}")
            print(f"Proofs Accuracy for {filename} → {theorem_name}: {proofs_accuracy}")
    
        print("=" * 50)
        print(f"Finished evaluating: {filename}")
        print("=" * 50)
        
    tactics_accuracy = calculate_accuracy(total_succ_tactics, total_tactics)
    proofs_accuracy = calculate_accuracy(total_succ_proofs, total_proofs)

    with open(RESULTS_FILE, 'a') as f:
        csv_writer = csv.writer(f)
        csv_writer.writerow(["Total", tactics_accuracy, proofs_accuracy])


if __name__ == "__main__":
    # Example usage
    evaluate_test_set()