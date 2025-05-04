import sys

def extract_unique_tactics(filepath):
    # Set to store unique tactics
    tactics_set = set()
    
    try:
        # Read the file
        with open(filepath, 'r') as file:
            for line in file:
                # Remove center dot and trim whitespace
                line = line.replace('·', '').strip()
                
                # Skip empty lines, comments, imports, namespace declarations, and theorem declarations
                if (not line or 
                    line.startswith('--') or 
                    line.startswith('import') or 
                    line.startswith('namespace') or
                    line.startswith('theorem')):
                    continue
                
                # Add non-empty lines to the set
                if line:
                    tactics_set.add(line)
    
    except FileNotFoundError:
        print(f"Error: File '{filepath}' not found")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading file: {e}")
        sys.exit(1)
    
    # Convert set to sorted list
    return sorted(list(tactics_set))

def main():
    # Check if file path is provided
    if len(sys.argv) != 2:
        print("Usage: python extract_tactics.py <path_to_lean_file>")
        sys.exit(1)
    
    filepath = sys.argv[1]
    tactics = extract_unique_tactics(filepath)
    
    # print("All unique tactics used in the file:")
    # for tactic in tactics:
    #     print(f"- {tactic}")
    return tactics

if __name__ == "__main__":
    main()