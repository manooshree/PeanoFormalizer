import re
import json
import sys
import csv
import argparse
from collections import defaultdict
from pathlib import Path

def parse_lean_proofs(content, filename):
    """Parse the Lean file content and extract theorem statements and proof steps."""
    theorem_pattern = r'(--\s*Proof Statement:\s*(.+?))\n(theorem\s+(\w+).+?)\s*:=\s*by\n((?:(?!--\s*Proof Statement)[\s\S])*)'
    theorems = re.finditer(theorem_pattern, content, re.MULTILINE)
    
    all_steps = []
    proof_groups = defaultdict(list)
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
            # First strip trailing whitespace
            line = line.rstrip()
            if not line:
                continue
                
            # Look for comments by stripping all whitespace first
            stripped_line = line.lstrip(' ·')  # Strip both spaces and bullet points
            if stripped_line.startswith('--'):
                # Save previous step if we have either comment and tactic
                if current_comment is not None and current_tactic:
                    # Join tactics with original indentation preserved
                    current_proof_steps.append({
                        "theorem": theorem_name,
                        "NL": current_comment,
                        "FL": '\n'.join(current_tactic).rstrip(),
                        "filename": filename
                    })
                    current_tactic = []
                current_comment = stripped_line[2:].strip()
            else:
                if current_comment is not None:
                    # Keep original line with indentation
                    current_tactic.append(line)
        
        # Don't forget the last step - important for single-tactic proofs!
        if current_comment is not None and current_tactic:
            current_proof_steps.append({
                "theorem": theorem_name,
                "NL": current_comment,
                "FL": '\n'.join(current_tactic).rstrip(),
                "filename": filename
            })
            
        proof_groups[theorem_name].extend(current_proof_steps)
        all_steps.extend(current_proof_steps)
    
    return all_steps, proof_groups, num_proofs

def save_as_json(data, output_file):
    """Save data as JSON file."""
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)

def save_as_csv(data, output_file):
    """Save data as CSV file."""
    with open(output_file, 'w', encoding='utf-8', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['theorem', 'NL', 'FL', 'filename'])
        for item in data:
            writer.writerow([item['theorem'], item['NL'], item['FL'], item['filename']])

def process_files(input_files, output_prefix):
    """Process multiple input files."""
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

    # Save outputs
    try:
        json_file = f"{output_prefix}.json"
        csv_file = f"{output_prefix}.csv"
        
        save_as_json(all_translation_pairs, json_file)
        save_as_csv(all_translation_pairs, csv_file)
        
        print(f"\nSummary:")
        print(f"Processed {total_files} files")
        print(f"Total proofs parsed: {total_proofs}")
        print(f"Total tactic pairs: {len(all_translation_pairs)}")
        print(f"Outputs saved to:")
        print(f"- JSON: {json_file}")
        print(f"- CSV: {csv_file}")
        
    except Exception as e:
        print(f"Error writing output files: {str(e)}")
        sys.exit(1)
        
    return all_translation_pairs, all_proofs_dict

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Parse Lean proofs to extract translation pairs')
    parser.add_argument('input_files', nargs='+', help='Path to one or more input Lean files')
    parser.add_argument('-o', '--output', default='leanopeano_addition',
                      help='Prefix for output files (default: leanopeano_addition)')
    
    args = parser.parse_args()
    process_files(args.input_files, args.output)