import os
import json
from openai import OpenAI
# from helper_scripts.rag import lean_rag
from dotenv import load_dotenv
from helper_scripts.lean_compile import lean_compile
import time
from dataset_scripts.parse_states import parse_unsolved_state, extract_intermediate_states
import random
import hashlib
import csv
from helper_scripts.cache import load_cache, save_cache, create_cache_key
from autoformalizer import autoformalize, autoformalize_colm, get_goal_state
from metric import check_if_correct
import re
from helper_scripts.clean_gpt_output import clean_formalized

import sys
sys.path.append('../')


def calculate_accuracy(num_succ, total):
    if total > 0:
        return f"{num_succ} / {total} = {num_succ / total:.2%}"
    else:
        return "0 / 0 = N/A"

def process_step(predicted_fl: list[str], prev_fl: list[str], fl_theorem_statement: str, theorem_name: str):
    # TODO: For actual experiment, remove next line (autoformalize function already does this)
    clean_predicted = clean_formalized(predicted_fl)
    prev_fl.append(clean_predicted)
    compiler_output = lean_compile(theorem_name, [fl_theorem_statement] + prev_fl)
    predicted_goal_state = parse_unsolved_state(compiler_output)
    error_matches = re.findall(r"error:(?!.*unsolved goals)", compiler_output.stdout or "")
    if error_matches:
        predicted_goal_state = "error"
    return predicted_goal_state, clean_predicted

def evaluate_proof(predicted_fl: list[str], true_fl: list[str], fl_theorem_statement: str, is_correct: list[bool] = []):
    results = []
    prev_fl = []
    proof_is_correct = True
    correct_proof = True
    theorem_name = fl_theorem_statement.split()[1]
    if not is_correct:
        correct_proof = False
        is_correct = [True] * len(predicted_fl) 
    for i, (predicted, true, correct) in enumerate(zip(predicted_fl, true_fl, is_correct)):
        predicted_goal_state, clean_predicted_fl = process_step(predicted, prev_fl, fl_theorem_statement, theorem_name)
        expected_lean_output = lean_compile(theorem_name, [fl_theorem_statement] + true_fl[:i+1])
        expected_goal_state = parse_unsolved_state(expected_lean_output)
        success = check_if_correct(true, clean_predicted_fl, expected_goal_state, predicted_goal_state)
        if not correct:
            success = predicted_goal_state == "error"
        result = {
            'step': i,
            'expected_tactic': true,
            'predicted_tactic': predicted,
            'clean_predicted_tactic': clean_predicted_fl,
            'expected_goal_state': expected_goal_state,
            'predicted_goal_state': predicted_goal_state,
            'is_successful': success
        }
        if correct_proof:
            result['is_correct_step'] = correct
        results.append(result)
        if not success:
            proof_is_correct = False
        num_successful = sum([res['is_successful'] for res in results])
        tactic_accuracy = calculate_accuracy(num_successful, len(results))
    return results, tactic_accuracy, proof_is_correct, num_successful

if __name__ == "__main__":
    predicted_fl = ["intro h", "rw [← is_zero_succ a]", "apply succ_inj at h", "exact h"]
    true_fl = ["intro h", "rw [← is_zero_succ a]", "apply succ_inj at h", "exact h"]
    fl_theorem_statement = "theorem t : a = b := by"
    print(evaluate_proof(predicted_fl, true_fl, fl_theorem_statement))