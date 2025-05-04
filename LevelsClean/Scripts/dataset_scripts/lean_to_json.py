import os
import json
from helper_scripts.lean_compile import lean_compile
from dataset_scripts.parse_states import parse_unsolved_state

import sys
sys.path.append('../')

input_directory = "NNG4/Game/LevelsClean/Datasets/full_clean_dataset/correct_lean"
output_directory = "NNG4/Game/LevelsClean/Datasets/full_clean_dataset/correct_json"
print("hello")
for file in os.listdir(input_directory):
    if not file.startswith("power_world_val"):
        continue
    data_json = {}
    with open(os.path.join(input_directory, file), "r") as f:
        data = f.read()
        data = data.split("\n")
        theorem_name = ""
        dev_name = ""
        current_proof = ""
        print(file)
        for i, line in enumerate(data):
            if line.strip().startswith("theorem") and "dev" not in line:
                theorem_name = line.strip().split()[1]
                data_json[theorem_name] = {}
                dev_name = ""
                current_proof = ""
                continue
            elif line.strip().startswith("theorem"):
                dev_name = line.strip().split()[1]
                current_proof = line
                out = lean_compile(dev_name, proof = current_proof)
                state = parse_unsolved_state(out)
                data_json[theorem_name][dev_name] = [
                    {
                        "NL": data[i - 1],
                        "FL": line,
                        "state": state
                    }
                ]
            elif dev_name and line and not line.strip().startswith("--"):
                current_proof += "\n" + line
                out = lean_compile(dev_name, proof = current_proof)
                state = parse_unsolved_state(out)
                data_json[theorem_name][dev_name].append(
                    {
                        "NL": data[i - 1],
                        "FL": line,
                        "state": state
                    }
                )
    with open(os.path.join(output_directory, file.replace(".lean", ".json")), "w") as f:
        json.dump(data_json, f, indent=4)
        