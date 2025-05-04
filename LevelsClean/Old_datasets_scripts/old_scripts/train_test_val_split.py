import re
import json
import sys
import csv
import argparse
import random
from pathlib import Path
from collections import defaultdict

def parse_lean_proofs(content, filename):
    """Parse the Lean file content and extract theorem statements and proof steps."""
    theorem_pattern = r'(--\s*Proof Statement:\s*(.+?))\n(theorem\s+(\w+).+?)\n((?:  .*\n)*)'
    theorems = re.finditer(theorem_pattern, content, re.MULTILINE)
    
    all_steps = []
    proof_groups = defaultdict(list)  # Group steps by theorem name
    num_proofs = 0
    
    for theorem_match in theorems:
        num_proofs += 1
        theorem_nl = theorem_match.group(2).strip()
        theorem_declaration = theorem_match.group(3).strip()
        theorem_name = theorem_match.group(4)
        proof_body = theorem_match.group(5)
        
        current_proof_steps = []
        # Add the theorem statement itself as the first pair
        current_proof_steps.append({
            "theorem": theorem_name,
            "NL": theorem_nl,
            "FL": theorem_declaration,
            "filename": filename
        })
        
        lines = proof_body.split('\n')
        current_comment = None
        current_tactic = []
        
        for line in lines:
            line = line.rstrip()
            if not line:
                continue
                
            if '--' in line:
                if current_comment is not None and current_tactic:
                    current_proof_steps.append({
                        "theorem": theorem_name,
                        "NL": current_comment,
                        "FL": '\n'.join(current_tactic).strip(),
                        "filename": filename
                    })
                    current_tactic = []
                current_comment = line.split('--', 1)[1].strip()
            else:
                if current_comment is not None:
                    current_tactic.append(line.strip())
        
        if current_comment is not None and current_tactic:
            current_proof_steps.append({
                "theorem": theorem_name,
                "NL": current_comment,
                "FL": '\n'.join(current_tactic).strip(),
                "filename": filename
            })
            
        proof_groups[theorem_name].extend(current_proof_steps)
        all_steps.extend(current_proof_steps)
    
    return all_steps, proof_groups, num_proofs

def split_train_test(all_proofs_dict):
    """Split proofs into train and test sets."""
    train_steps = []
    test_steps = []
    
    # Group proofs by filename
    proofs_by_file = defaultdict(list)
    for theorem, steps in all_proofs_dict.items():
        if steps:  # Check if steps exist
            filename = steps[0]['filename']
            proofs_by_file[filename].append((theorem, steps))
    
    # For each file, randomly select one proof for test set
    for filename, proofs in proofs_by_file.items():
        test_theorem, test_proof = random.choice(proofs)
        
        for theorem, steps in proofs:
            if theorem == test_theorem:
                test_steps.extend(steps)
            else:
                train_steps.extend(steps)
                
    return train_steps, test_steps

def save_as_json(data, output_file):
    """Save data as JSON file."""
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

def save_as_csv(data, output_file):
    """Save data as CSV file."""
    csv_file = output_file.replace('.json', '.csv')
    with open(csv_file, 'w', encoding='utf-8', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['theorem', 'NL', 'FL', 'filename'])
        for item in data:
            writer.writerow([item['theorem'], item['NL'], item['FL'], item['filename']])
    return csv_file

def process_files(input_files, output_prefix):
    """Process multiple input files and create train/test splits."""
    all_translation_pairs = []
    all_proofs_dict = defaultdict(list)
    total_proofs = 0
    total_files = 0
    
    for input_file in input_files:
        try:
            with open(input_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            translation_pairs, proof_groups, num_proofs = parse_lean_proofs(content, Path(input_file).name)
            all_translation_pairs.extend(translation_pairs)
            for theorem, steps in proof_groups.items():
                all_proofs_dict[theorem].extend(steps)
            total_proofs += num_proofs
            total_files += 1
            
            print(f"Processed {input_file}: {num_proofs} proofs, {len(translation_pairs)} tactic pairs")
            
        except FileNotFoundError:
            print(f"Warning: Input file '{input_file}' not found, skipping...")
        except Exception as e:
            print(f"Warning: Error processing '{input_file}': {str(e)}, skipping...")
    
    if total_files == 0:
        print("Error: No valid input files found")
        sys.exit(1)
        
    # Split into train and test
    train_data, test_data = split_train_test(all_proofs_dict)
    
    try:
        # Save train data
        train_json = f"{output_prefix}_train.json"
        train_csv = save_as_csv(train_data, train_json)
        save_as_json(train_data, train_json)
        
        # Save test data
        test_json = f"{output_prefix}_test.json"
        test_csv = save_as_csv(test_data, test_json)
        save_as_json(test_data, test_json)
        
        print(f"\nSummary:")
        print(f"Processed {total_files} files")
        print(f"Total proofs parsed: {total_proofs}")
        print(f"Train set size: {len(train_data)} tactic pairs")
        print(f"Test set size: {len(test_data)} tactic pairs")
        print(f"Outputs saved to:")
        print(f"- Train: {train_json}, {train_csv}")
        print(f"- Test: {test_json}, {test_csv}")
        
    except Exception as e:
        print(f"Error writing output files: {str(e)}")
        sys.exit(1)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Convert Lean proofs to JSON and CSV translation pairs with train/test split')
    parser.add_argument('input_files', nargs='+', help='Path to one or more input Lean files')
    parser.add_argument('-o', '--output', default='leanopeano',
                      help='Prefix for output files (default: leanopeano)')
    
    args = parser.parse_args()
    process_files(args.input_files, args.output)