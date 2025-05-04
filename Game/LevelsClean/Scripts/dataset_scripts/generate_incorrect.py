import json
import os
import random

# Input: correct_json
input_directory = "NNG4/Game/LevelsClean/Datasets/full_clean_dataset/correct_json"
# Output: incorrect_lean
output_directory = "NNG4/Game/LevelsClean/Datasets/full_clean_dataset/non-correct_lean"


for file in os.listdir(input_directory):
    print(file)
    if file.endswith(".json"):
        with open(os.path.join(input_directory, file), "r") as f:
            data = json.load(f)

        theorems_classes = data
        incorrect_proofs = []
        proofs_to_del = []
        for theorem_class, theorems in theorems_classes.items():    
            for theorem, proof_lines in theorems.items():
                n = len(proof_lines) - 1
                if n > 4:
                    skipped_index = n - random.randint(1, 3)
                elif n == 4:
                    skipped_index = n - random.randint(1, 2)
                elif n == 3 or n == 2:
                    skipped_index = 2
                else: 
                    proofs_to_del.append((theorem_class, theorem))
                    continue
                proof_lines.pop(skipped_index)
                for i, x in enumerate(proof_lines):
                    x["is_correct"] = True if i < skipped_index else False
        for theorem_class, theorem in proofs_to_del:
            del theorems_classes[theorem_class][theorem]
        with open(os.path.join(input_directory, file), "w") as f:
            json.dump(theorems_classes, f, indent=4)
