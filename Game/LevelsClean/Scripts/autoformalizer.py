import time
from openai import OpenAI
from helper_scripts.lean_compile import lean_compile
from dataset_scripts.parse_states import parse_unsolved_state
from helper_scripts.cache import save_cache, create_cache_key, load_cache
from dotenv import load_dotenv
import os
import json
from helper_scripts.clean_gpt_output import clean_formalized

load_dotenv("NNG4/.env")
client = OpenAI(api_key="")

# Create cache directory if does not exist
GPT_CACHE_DIR = 'NNG4/Game/LevelsClean/saving_outputs/GPT_cache'
os.makedirs(GPT_CACHE_DIR, exist_ok=True)

# LLM Cache file paths
TACTIC_CACHE_FILE = os.path.join(GPT_CACHE_DIR, 'tactic_cache.json')
GOAL_CACHE_FILE = os.path.join(GPT_CACHE_DIR, 'goal_cache.json')

# loading LLM cache
tactic_cache = load_cache(TACTIC_CACHE_FILE)
goal_cache = load_cache(GOAL_CACHE_FILE)

# Load all theorems
with open('NNG4/Game/LevelsClean/Datasets/whole_proofs.json', 'r') as f:
    whole_theorems = json.load(f)
# Load theorem and tactic dictionaries
with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/theorem_dict.json', 'r') as f:
    theorem_dict = json.load(f)
with open('NNG4/Game/LevelsClean/Datasets/theorem_tactic_dict/tactic_dict.json', 'r') as f:
    tactic_dict = json.load(f)

# predict next goal state using LLM
def get_goal_state(nl_statement: str, prev_goal: str, theorem_name: str):
    global goal_cache
    
    # Create a cache key
    cache_data = {
        "nl_statement": nl_statement,
        "prev_goal": prev_goal,
        "theorem_name": theorem_name
    }
    cache_key = create_cache_key(cache_data)
    
    # Check if result is in cache
    if cache_key in goal_cache:
        return goal_cache[cache_key]

    prompt_predict_next_state = f"""
    Here is the current proof state:
    {prev_goal}
    
    I need to predict what the state will be after applying this step:
    "{nl_statement}"
    
    INSTRUCTIONS:
    1. Analyze the current state and the natural language description
    2. Predict what the mathematical expression will look like after this step
    3. Output ONLY the predicted state with no additional text or explanation
    4. Make sure to include brackets when necessary
    """
    
    if prev_goal != "error":
        response = client.chat.completions.create(
                model="gpt-4",
                messages=[{"role": "user", "content": prompt_predict_next_state}]
        )
        result = response.choices[0].message.content.strip()
    else:
        result = "Ignore the predicted next state. Use the other information to predict the next step."
    
    # Save to cache
    goal_cache[cache_key] = result
    save_cache(goal_cache, GOAL_CACHE_FILE)
    
    return result


def autoformalize(nl_statement: str, 
                        theorem_name: str,
                        prev_goal: str = "",
                        predicted_next_state: str = "",
                        prev_fl: list = [],
                        prev_nl: list = [],
                        all_student_steps: str = "",
                        three_pass: bool = False,
                        is_five_shot: bool = False,
                        five_shot_rag: bool = False,
                        check_next_goal: bool = False):
    global tactic_cache, theorem_dict, tactic_dict, whole_theorems
    
    # Create a cache key
    cache_data = {
        "nl_statement": nl_statement,
        "prev_goal": prev_goal, 
        "theorem_name": theorem_name,
        "predicted_next_state": predicted_next_state,
        "prev_fl": prev_fl,
        "prev_nl": prev_nl,
        "three_pass": three_pass,
        "all_student_nl": all_student_steps,
        "is_five_shot": is_five_shot,
        "five_shot_rag": five_shot_rag,
        "check_next_goal": check_next_goal,
        "colm": False
    }
    cache_key = create_cache_key(cache_data)
    
    # Check if result is in cache
    if cache_key in tactic_cache:
        print("CACHE HIT")
        return tactic_cache[cache_key]
    
    print("calling theorem", theorem_name)
    theorem_statement_NL = whole_theorems[theorem_name].split("\n")[0]
    theorem_statement_FL = whole_theorems[theorem_name].split("\n")[1]
    preamble = f"""
        Convert proofs written in Natural Language by students into Lean4 code

        The name of the theorem we are working with is {theorem_name}.
        This is the theorem statement in natural language: {theorem_statement_NL}
        This is the theorem statement in formal language: {theorem_statement_FL}     

        This is one example of the proof of {theorem_name} with alternating natural language and formal language steps (each formal line of lean conde directly follows its corresponding natural language line of lean code):

        {whole_theorems[theorem_name]}

        Your proofs can make use of the following construction rules and inference rules:
        {theorem_dict}

        Your response must be a tactic proof in the Natural Numbers Game 4 DSL. This DSL is built from the following tactics (arguments indicated by "name_of_theorem" ):
        {tactic_dict}
    """
    postamble = f"""
        You're response must be written as a single line of Lean tactic code, as used in the body of a by block of a Lean theorem. It should match the structure of Lean DSL tactic proofs, such as:
        intro h 
        rw [← is_zero_succ a]
        apply succ_inj at h
        exact h
        contrapose! h

        Note: Only 1 lean tactic, do not write multiple lean tactics that are comma seperated.

        Each line must correspond to a valid Lean tactic (e.g. intro, rw, apply, exact, trivial, etc.), optionally with arguments in parentheses or brackets, and formatted consistently with Lean4's syntax.

        DO *NOT* wrap your answer in markdown syntax, e.g. '''lean '''. It must be simply a Lean tactic script that can be inserted into a proof.
    """
    prev_goal_prompt = f"""
        The lean state has information about theorems or variables that have been introduced which might be used in the next step.
        The current state in lean is:
        {prev_goal}
    """
    predicted_next_state_prompt = f"""
        After applying the natural language step "{nl_statement}" to the current state, the predicted next state in lean is:
        {predicted_next_state}
    """
    prev_fl_prompt = f"""
        The previous student lines of Lean code are:
        {prev_fl}
    """
    prev_nl_prompt = f"""
        The previous student lines of natural language are:
        {prev_nl}
    """
    all_student_nl_prompt = f"""
        The entire student proof in natural language is:
        {all_student_steps}
    """
    five_shot_prompt = f"""
        Here are some examples. NOTE: These are just examples. The correct Lean4 code may not necessarily use the propositions shown in these proofs.

        Example 1:
        Input: -- Rewrite the LHS pred (succ a) with the given statement that succ a = succ b, LHS is now pred (succ b)
        Output: rw [h]

        Example 2:
        Input: -- Simplify the LHS 0 * d + 0 to 0 + 0 using the inductive hypothesis
        Output: rw [hd]

        Example 3: 
        Input: -- Assume that the hypothesis 'h' is true, that is, a + succ d = 0. The goal now is to prove that a = 0.
        Output: rw [add_zero] at h

        Example 4:
        Input:  -- Rewrite the left hand side using the identity that any natural number to the power of 0 is 1
        Output: rw [pow_zero]

        Example 5:
        Input: -- Use the case of a + b to simplify the goal to equal z = x + (a + b).
        Output: use a + b
    """

    system_prompt = preamble
    if prev_goal:
        system_prompt += "\n" + prev_goal_prompt
    if predicted_next_state:
        system_prompt += "\n" + predicted_next_state_prompt
    if prev_fl:
        system_prompt += "\n" + prev_fl_prompt
    if prev_nl:
        system_prompt += "\n" + prev_nl_prompt
    if all_student_nl_prompt:
        system_prompt += "\n" + all_student_nl_prompt
    system_prompt += "\n" + postamble
    if five_shot_rag:
        # set up rag and change five_shot_prompt to be have rag inputs
        ...
    if is_five_shot:
        system_prompt += "\n" + five_shot_prompt

    prompt = f''' The current state of the proof is 
                    {prev_goal}
                  The natural language statement that we want to formalize {nl_statement}'''

    prompt_error = lambda compiler_error : f'''
        The line of Lean code you provided did not compile.
        Error message: {compiler_error}

        Please revise your output to fix this error.
        Remember to formalize this natural language statement: {nl_statement}

        Provide ONLY the corrected line of Lean code with no additional text or formatting.
    '''

    try:
        messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": prompt}]
        
        response = client.chat.completions.create(
            model="gpt-4",
            messages=messages
        )
        formalized = response.choices[0].message.content.strip()
        if three_pass:
            proof_to_compiler = prev_fl + [formalized]
            compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
            i = 3
            while compiler_output.stdout and "unsolved goals" not in compiler_output.stdout:
                # print(theorem_name, compiler_output.stdout)
                messages.append({"role": "assistant", "content": formalized})
                messages.append({"role": "user", "content": prompt_error(compiler_output.stdout)})
                response = client.chat.completions.create(
                    model="gpt-4",
                    messages=messages
                )
                formalized = response.choices[0].message.content.strip() 
                proof_to_compiler = prev_fl + [formalized]
                compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
                if i <= 0:
                    print("FAILED")
                    break
                i -= 1
        if check_next_goal:
            # TODO: Implement check_next_goal
            ...
    except Exception as e:
        print(f"Rate limit hit, sleeping for 40 seconds", e)
        time.sleep(40)
    
    # Save to cache
    tactic_cache[cache_key] = formalized
    save_cache(tactic_cache, TACTIC_CACHE_FILE)

    return clean_formalized(formalized)

def autoformalize_colm(nl_statement: str, 
                        theorem_name: str,
                        prev_goal: str = "",
                        predicted_next_state: str = "",
                        prev_fl: list = [],
                        prev_nl: list = [],
                        all_student_steps: str = "",
                        three_pass: bool = False,
                        is_five_shot: bool = False,
                        five_shot_rag: bool = False,
                        check_next_goal: bool = False,
                        use_prev_fl: bool = True):
    global tactic_cache, theorem_dict, tactic_dict, whole_theorems
    
    # Create a cache key
    cache_data = {
        "nl_statement": nl_statement,
        "prev_goal": prev_goal, 
        "theorem_name": theorem_name,
        "predicted_next_state": predicted_next_state,
        "prev_fl": prev_fl if use_prev_fl else [],
        "prev_nl": prev_nl,
        "three_pass": three_pass,
        "all_student_nl": all_student_steps,
        "is_five_shot": is_five_shot,
        "five_shot_rag": five_shot_rag,
        "check_next_goal": check_next_goal
    }
    cache_key = create_cache_key(cache_data)
    
    # Check if result is in cache
    if cache_key in tactic_cache:
        print("CACHE HIT")
        return tactic_cache[cache_key]
    
    print("calling theorem", theorem_name)
    theorem_statement_NL = whole_theorems[theorem_name].split("\n")[0]
    theorem_statement_FL = whole_theorems[theorem_name].split("\n")[1]
    
    preamble = f"""
        We are proving {theorem_name}.
        This is one example of the proof of {theorem_name}:

        {whole_theorems[theorem_name]}
        This is the theorem statement in natural language: {theorem_statement_NL}
        This is the theorem statement in formal language: {theorem_statement_FL}

        Here are some definitions of theorems and tactics to help you choose the correct example:
        {theorem_dict}
        {tactic_dict}

        Given a natural language mathematical statement, convert it to formal Lean theorem syntax.
    """
    postamble = f"""
        Give me only the line of Lean code that is the formalized version of the natural language statement.
        Do not include any other text or formatting.
    """
    prev_goal_prompt = f"""
        The lean state has information about theorems or variables that have been introduced which might be used in the next step.
        The current state in lean is:
        {prev_goal}
    """
    predicted_next_state_prompt = f"""
        After applying the natural language step "{nl_statement}" to the current state, the predicted next state in lean is:
        {predicted_next_state}
    """
    prev_fl_prompt = f"""
        The previous student lines of Lean code are:
        {prev_fl}
    """
    prev_nl_prompt = f"""
        The previous student lines of natural language are:
        {prev_nl}
    """
    all_student_nl_prompt = f"""
        The entire student proof in natural language is:
        {all_student_steps}
    """

    system_prompt = preamble
    if prev_goal:
        system_prompt += "\n" + prev_goal_prompt
    if predicted_next_state:
        system_prompt += "\n" + predicted_next_state_prompt
    if use_prev_fl and prev_fl:
        system_prompt += "\n" + prev_fl_prompt
    if prev_nl:
        system_prompt += "\n" + prev_nl_prompt
    if all_student_nl_prompt:
        system_prompt += "\n" + all_student_nl_prompt
    system_prompt += "\n" + postamble
        
    prompt = f''' The current state of the proof is 
                    {prev_goal}
                  The natural language statement that we want to formalize {nl_statement}'''

    prompt_compile_error = lambda compiler_error : f'''
        The line of Lean code you provided did not compile.
        Error message: {compiler_error}

        Please revise your output to fix this error.
        Remember to formalize this natural language statement: {nl_statement}

        Provide ONLY the corrected line of Lean code with no additional text or formatting.
    '''
    prompt_goal_state_error = f'''
        The line of Lean code you provided did not produce the predicted goal state.
        The predicted goal state in lean is:
        {predicted_next_state}

        Please revise your output to fix this error.
        Remember to formalize this natural language statement: {nl_statement}

        Provide ONLY the corrected line of Lean code with no additional text or formatting.
    '''
    try:
        messages = [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": prompt}]
        
        response = client.chat.completions.create(
            model="gpt-4",
            messages=messages
        )
        formalized = response.choices[0].message.content.strip()
        if three_pass:
            proof_to_compiler = prev_fl + [formalized]
            compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
            i = 3
            while compiler_output.stdout and "unsolved goals" not in compiler_output.stdout:
                # print(theorem_name, compiler_output.stdout)
                messages.append({"role": "assistant", "content": formalized})
                messages.append({"role": "user", "content": prompt_compile_error(compiler_output.stdout)})
                response = client.chat.completions.create(
                    model="gpt-4",
                    messages=messages
                )
                formalized = response.choices[0].message.content.strip() 
                proof_to_compiler = prev_fl + [formalized]
                compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
                if i <= 0:
                    print("FAILED")
                    break
                i -= 1
        if check_next_goal:
            if not prev_fl:
                raise ValueError("prev_fl must be not be empty when check_next_goal is True")
            proof_to_compiler = prev_fl + [formalized]
            compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
            goal_state = parse_unsolved_state(compiler_output)
            i = 3
            while goal_state != predicted_next_state:
                # print(theorem_name, compiler_output.stdout)
                messages.append({"role": "assistant", "content": formalized})
                messages.append({"role": "user", "content": prompt_goal_state_error})
                response = client.chat.completions.create(
                    model="gpt-4",
                    messages=messages
                )
                formalized = response.choices[0].message.content.strip() 
                proof_to_compiler = prev_fl + [formalized]
                compiler_output = lean_compile(f"run_time_error_passes_{theorem_name}", proof_to_compiler)
                goal_state = parse_unsolved_state(compiler_output)
                if i <= 0:
                    print("FAILED")
                    break
                i -= 1
    except Exception as e:
        print(f"Rate limit hit, sleeping for 40 seconds", e)
        time.sleep(40)
    
    # Save to cache
    tactic_cache[cache_key] = formalized
    save_cache(tactic_cache, TACTIC_CACHE_FILE)
    
    return clean_formalized(formalized)