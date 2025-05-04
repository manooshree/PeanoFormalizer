import os
import json
from pathlib import Path

def extract_theorems_from_clean(file_path):
    theorems = {}
    current_theorem = ""
    current_name = ""
    in_theorem = False
    
    with open(file_path, 'r') as f:
        lines = f.readlines()
    
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        
        # Skip empty lines
        if not line:
            if in_theorem:
                # Store theorem if we were collecting one
                if current_name and "_persona" not in current_name and "_logical" not in current_name:
                    theorems[current_name] = current_theorem
            in_theorem = False
            current_theorem = ""
            current_name = ""
            i += 1
            continue
        
        # Look for theorem declarations
        
        if line.startswith('theorem '):
            # Check for comments before this theorem
            comment_text = ""
            j = i - 1
            # Look backward for comments
            # while j >= 0 and lines[j].strip().startswith('--'):
            comment_text = lines[j].strip() + "\n" + comment_text
            
            # Store previous theorem if exists
            if in_theorem and current_name and "_persona" not in current_name and "_logical" not in current_name:
                theorems[current_name] = current_theorem
            
            in_theorem = True
            # Include comments at the start of the theorem text
            current_theorem = comment_text + line + "\n" if comment_text else line + "\n"
            # Extract theorem name
            current_name = line.split()[1]
            i += 1

            continue


        if in_theorem:
            current_theorem += line + "\n"
        
        i += 1
    
    # Handle last theorem
    if in_theorem and current_name and "_persona" not in current_name and "_logical" not in current_name and not current_name[-2].isdigit():
        theorems[current_name] = current_theorem
        
    return theorems

def process_clean_files():
    clean_files = []
    base_path = Path("NNG4/Game/LevelsClean/Datasets/full_clean_dataset/correct_lean")
    
    # Find all .lean files in LevelsClean directory
    for file in base_path.rglob("*.lean"):
        clean_files.append(str(file))
    
    
    all_theorems = {}
    
    for file in clean_files:
        theorems = extract_theorems_from_clean(file)
        if theorems:
            all_theorems.update(theorems)
            
    # Save to JSON file
    output_file = "NNG4/Game/LevelsClean/Datasets/whole_proofs.json"
    os.makedirs(os.path.dirname(output_file), exist_ok=True)
    
    with open(output_file, 'w') as f:
        json.dump(all_theorems, f, indent=2)
        
    print(f"Extracted {len(all_theorems)} theorems with comments to {output_file}")

if __name__ == "__main__":
    process_clean_files()
    # file_path = "NNG4/Game/LevelsClean/AdvMultiplicationClean.lean"
    # theorems = extract_theorems_from_clean(file_path)
    # print(len(theorems))
    # with open("NNG4/Game/LevelsClean/Datasets/whole_proofs_2.json", "r") as f:
    #     whole_theorems = json.load(f)
    # print(len(whole_theorems))
    # whole_theorems.update(theorems)
    # print(len(whole_theorems))
    # with open("NNG4/Game/LevelsClean/Datasets/whole_proofs_2.json", "w") as f:
    #     json.dump(whole_theorems, f, indent=2)
