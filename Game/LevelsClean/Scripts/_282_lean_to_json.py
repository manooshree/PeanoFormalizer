import os
import json
import random
from helper_scripts.lean_compile import lean_compile
from dataset_scripts.parse_states import parse_unsolved_state

import sys
sys.path.append('../')

input_directory = "Game/LevelsClean/Datasets/full_clean_dataset/correct_lean"
output_directory = "Game/LevelsClean/Datasets/full_clean_dataset/_282_correct_json"

# set random seed 
random.seed(27)

train_json = {}
val_json = {}
test_json = {}

print("hello")
for file in os.listdir(input_directory):
    if not file.endswith(".lean"):
        continue

    data_json = {}
    with open(os.path.join(input_directory, file), "r") as f:
        data = f.read().split("\n")
        theorem_name = ""
        current_key = ""
        current_proof = ""
        print(file)
        for i, line in enumerate(data):
            if line.strip().startswith("theorem"):
                current_key = line.strip().split()[1]  # e.g. zero_add or zero_add__dev_1
                current_proof = line
                out = lean_compile(current_key, proof=current_proof)
                state = parse_unsolved_state(out)

                if "dev" not in current_key:
                    theorem_name = current_key
                    data_json[theorem_name] = {}
                    data_json[theorem_name][current_key] = [{
                        "theorem": current_key,
                        "NL": data[i - 1],
                        "FL": line,
                        "state": state
                    }]
                else:
                    data_json[theorem_name][current_key] = [{
                        "theorem": current_key,
                        "NL": data[i - 1],
                        "FL": line,
                        "state": state
                    }]
            elif current_key and line and not line.strip().startswith("--"):
                current_proof += "\n" + line
                out = lean_compile(current_key, proof=current_proof)
                state = parse_unsolved_state(out)
                data_json[theorem_name][current_key].append({
                    "theorem": current_key,
                    "NL": data[i - 1],
                    "FL": line,
                    "state": state
                })

    # train/test/val split logic
    for theorem_name, proof_variants in data_json.items():
        all_proof_names = list(proof_variants.keys())
        selected = random.choice(all_proof_names)
        remaining = [p for p in all_proof_names if p != selected]

        target_split = val_json if random.random() < 0.5 else test_json
        if theorem_name not in target_split:
            target_split[theorem_name] = {}
        target_split[theorem_name][selected] = proof_variants[selected]

        if theorem_name not in train_json:
            train_json[theorem_name] = {}
        for p in remaining:
            train_json[theorem_name][p] = proof_variants[p]


with open(os.path.join(output_directory, "correct_train.json"), "w") as f:
    json.dump(train_json, f, indent=4)
with open(os.path.join(output_directory, "correct_val.json"), "w") as f:
    json.dump(val_json, f, indent=4)
with open(os.path.join(output_directory, "correct_test.json"), "w") as f:
    json.dump(test_json, f, indent=4)

# summary 
print("Dataset split complete!")
print(f"Train theorems: {len(train_json)} proofs: {sum(len(v) for v in train_json.values())}")
print(f"Validation theorems: {len(val_json)} proofs: {sum(len(v) for v in val_json.values())}")
print(f"Test theorems: {len(test_json)} proofs: {sum(len(v) for v in test_json.values())}")
