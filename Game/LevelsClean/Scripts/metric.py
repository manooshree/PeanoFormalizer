def check_individual_goal_state(ground_truth_goal: str, predicted_goal: str):
    # check if goal state length is the same
    if len(ground_truth_goal.split()) != len(predicted_goal.split()):
        print("different length")
        return False
    mappings = {}
    matching_chars = ["*", "^", "+", "-", "=", "/", "<", ">", "≤", "≥", "True", "False"]
    ground_truth_goal = ground_truth_goal.replace("(", "( ").replace(")", " )")
    predicted_goal = predicted_goal.replace("(", "( ").replace(")", " )")
    for i, (g, p) in enumerate(zip(ground_truth_goal.split(), predicted_goal.split())):
        print(g, p)
        print(mappings)
        # check if any math symbol is in the token (these should perfectly match)
        if any(c in g for c in matching_chars) or any(c in p for c in matching_chars) or g.isdigit() or p.isdigit():
            if g != p:
                print("different with math char")
                return False
            continue
        # check if all alpha portions of the token are in the mappings (add them if not)
        if g not in mappings:
            mappings[g] = p
        # check if the mapping is consistent between the two alpha tokens
        elif mappings[g] != p:
            print("different second mapping", g, p, mappings[g])
            print(mappings)
            return False
    print("correct")
    return True

def check_goal_state_match(ground_truth_goal: str, predicted_goal: str):
    ground_truth_goal = ground_truth_goal.strip("\n")
    predicted_goal = predicted_goal.strip("\n")
    if ground_truth_goal == predicted_goal:
        print("exact same")
        return True
    true_goal_states = ground_truth_goal.split("case")
    predicted_goal_states = predicted_goal.split("case")
    for true_goal, predicted_goal in zip(true_goal_states, predicted_goal_states):
        if not check_individual_goal_state(true_goal, predicted_goal):
            return False
    return True
    

def check_tactics_match(ground_truth: str, predicted: str):
    if ground_truth.strip() == predicted.strip(): 
        return True
    if ground_truth.strip() in predicted.strip(): 
        return True
    return False


def check_if_correct(ground_truth: str, predicted: str, ground_truth_goal: str, predicted_goal: str):
    return check_tactics_match(ground_truth, predicted) or check_goal_state_match(ground_truth_goal, predicted_goal)
    

if __name__ == "__main__":
    predicted_goal = """
        y (z) : ℕ
        h : z = (y + 2)
        ⊢ z = y + 2
    """
    ground_truth_goal = """
        y (x) : ℕ
        h : z = (y + 2)
        ⊢ x = y + 2
    """
    # print(check_if_correct(ground_truth, predicted, ground_truth_goal, predicted_goal))