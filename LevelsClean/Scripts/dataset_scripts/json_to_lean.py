import json
import os
import random
input_directory = "NNG4/Game/LevelsClean/Datasets/full_clean_dataset/non-correct_json"
output_directory = "NNG4/Game/LevelsClean/Datasets/full_clean_dataset/non-correct_lean"

# use if json is in old format
def seperate_proofs(data):
    theorems = {}
    current_theorem = ""
    theorem_class = "AAA"
    for item in data:
        if not item["theorem"].startswith(theorem_class):
            theorem_class = item["theorem"]
            theorems[theorem_class] = {}
        if item["theorem"] != theorem_class:
            if item["theorem"] != current_theorem:
                current_theorem = item["theorem"]
                theorems[theorem_class][current_theorem] = []
            theorems[theorem_class][current_theorem].append(item)
    return theorems

def json_to_lean(data):
    proof_str = ""
    for proof_class, proofs in data.items():
        for proof, proof_lines in proofs.items():
            for line in proof_lines:
                proof_str += f"{line['NL']}\n  "
                proof_str += f"{line['FL']}\n  "
            proof_str += "\n"
    return proof_str

for file in os.listdir(input_directory):
    print(file)
    if file.endswith(".json"):
        with open(os.path.join(input_directory, file), "r") as f:
            data = json.load(f)
        # if data in old format, use seperate_proofs
        output_file = file.replace(".json", ".lean")
        with open(os.path.join(output_directory, output_file), "w") as f:
            f.write(json_to_lean(data))
