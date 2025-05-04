import csv
import os

def save_full_results(results, nl_steps, output_dir, theorem_name, consolidated_csv_file, is_correct: bool):
    csv_file_path = os.path.join(output_dir, f"{theorem_name}.csv")
    csv_file_exists = os.path.exists(csv_file_path)
    consolidated_csv_exists = os.path.exists(consolidated_csv_file)
    
    # Open both the world-specific CSV and the consolidated CSV
    csv_file = open(csv_file_path, 'a', newline='')
    consolidated_csv = open(consolidated_csv_file, 'a', newline='')
    
    csv_writer = csv.writer(csv_file)
    consolidated_writer = csv.writer(consolidated_csv)
    
    # Write headers if files are new
    headers = ['Theorem Name', 'Natural Language', 'Predicted Formalization', 
                            'True Tactic', 'Predicted Goal State', 'True Goal State']
    if not is_correct:
        headers.append('Is Correct Step')
    headers.append('Is Successful')
    if not csv_file_exists:
        csv_writer.writerow(headers)
    if not consolidated_csv_exists:
        consolidated_writer.writerow(headers)
    
    for res, nl_step in zip(results, nl_steps):
        row_data = [
            theorem_name,
            nl_step,
            res['predicted_tactic'],
            res['expected_tactic'],
            res['predicted_goal_state'],
            res['expected_goal_state'],
        ]
        if not is_correct:
            row_data.append(res['is_correct_step'])
        row_data.append('Yes' if res['is_successful'] else 'No')

        csv_writer.writerow(row_data)
        consolidated_writer.writerow(row_data)

    csv_file.close()
    consolidated_csv.close()
    