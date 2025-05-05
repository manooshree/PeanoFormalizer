import os
os.environ["CUDA_VISIBLE_DEVICES"] = "1"
import sys
import json
import torch
# torch.cuda.set_device(1)
print(f"CUDA available: {torch.cuda.is_available()}")
print(f"CUDA device count: {torch.cuda.device_count()}")
if torch.cuda.is_available():
    for i in range(torch.cuda.device_count()):
        print(f"Device {i}: {torch.cuda.get_device_name(i)}")
import matplotlib.pyplot as plt
from datasets import Dataset
from transformers import (
    AutoModelForCausalLM,
    AutoTokenizer,
    TrainingArguments,
    Trainer,
    DataCollatorForLanguageModeling,
    TrainerCallback
)
from peft import (
    get_peft_model,
    LoraConfig,
    TaskType,
    prepare_model_for_kbit_training
)
from transformers import BitsAndBytesConfig


sys.path.append('../')



MODEL_NAME = "deepseek-ai/DeepSeek-Prover-V1.5-SFT"
TRAIN_DATASET_PATH = "Game/LevelsClean/Datasets/full_clean_dataset/_282_correct_json/correct_train.json"  # Change this to your training dataset path
VAL_DATASET_PATH = "Game/LevelsClean/Datasets/full_clean_dataset/_282_correct_json/correct_val.json"    # Change this to your validation dataset path
OUTPUT_DIR = "deepseek-prover-lora-3"
LORA_R = 64
HF_TOKEN = "" # Insert your HF token 
LORA_ALPHA = 128 # 2x Lora rank 
LORA_DROPOUT = 0.1
LEARNING_RATE = 3e-5 # small learning rate to accommodate small training set
BATCH_SIZE = 4
EPOCHS = 8 # epochs at 8 to accommodate small training set
MAX_LENGTH = 512

class LossCallback(TrainerCallback):
    """Custom callback to track and plot training and evaluation loss"""
    def __init__(self):
        self.training_losses = []
        self.eval_losses = []
        self.learning_rates = []
        self.epochs = []
        self.current_epoch = 0
        self.epoch_training_loss_sum = 0
        self.epoch_step_count = 0
        
    def on_log(self, args, state, control, logs=None, **kwargs):
        """Called each time trainer.log is called"""
        if logs is None:
            return
        
        if 'loss' in logs:
            step = state.global_step
            loss = logs['loss']
            print(f"Step {step}: Training loss = {logs['loss']:.4f}")
            
            self.epoch_training_loss_sum += loss
            self.epoch_step_count += 1

            if 'learning_rate' in logs:
                self.learning_rates.append((step, logs['learning_rate']))
  
        if 'eval_loss' in logs:
            self.current_epoch += 1
            eval_loss = logs['eval_loss']

            avg_train_loss = self.epoch_training_loss_sum / max(1, self.epoch_step_count)
            
            self.epochs.append(self.current_epoch)
            self.training_losses.append(avg_train_loss)
            self.eval_losses.append(eval_loss)
            
            self.epoch_training_loss_sum = 0
            self.epoch_step_count = 0
            
            print(f"\n===== Epoch {self.current_epoch} =====")
            print(f"Training Loss: {avg_train_loss:.4f}")
            print(f"Validation Loss: {eval_loss:.4f}")
            if self.learning_rates:
                print(f"Current Learning Rate: {self.learning_rates[-1][1]:.8f}\n")
            
            # Create and save plots after each epoch
            self._create_loss_plot()
            self._create_lr_plot()
    
    def _create_loss_plot(self):
        """Create and save loss plots"""
        plt.figure(figsize=(10, 6))
        plt.plot(self.epochs, self.training_losses, 'b-', label='Training Loss')
        plt.plot(self.epochs, self.eval_losses, 'r-', label='Validation Loss')
        plt.xlabel('Epoch')
        plt.ylabel('Loss')
        plt.title('Training and Validation Loss')
        plt.legend()
        plt.grid(True)
        
        
        os.makedirs('plots', exist_ok=True)
        plt.savefig(f'plots/loss_plot_epoch_{self.current_epoch}.png')
        plt.close()
        
        print(f"Loss plot saved to plots/loss_plot_epoch_{self.current_epoch}.png")
        
    def _create_lr_plot(self):
        """Create and save learning rate plot"""
        if not self.learning_rates:
            return
            
        steps, rates = zip(*self.learning_rates)
        
        plt.figure(figsize=(10, 6))
        plt.plot(steps, rates, 'g-')
        plt.xlabel('Step')
        plt.ylabel('Learning Rate')
        plt.title('Learning Rate Schedule (Cosine)')
        plt.grid(True)
        
        # Save plot
        os.makedirs('plots', exist_ok=True)
        plt.savefig(f'plots/lr_plot_epoch_{self.current_epoch}.png')
        plt.close()
        
        print(f"Learning rate plot saved to plots/lr_plot_epoch_{self.current_epoch}.png")

def prepare_dataset(file_path):
    with open(file_path, 'r') as f:
        raw_data = json.load(f)

    formatted_data = []
    for theorem_group in raw_data.values():
        for proof in theorem_group.values():
            for step in proof[1:]:  # Skip first step (theorem declaration)
                nl = step["NL"]
                fl = step["FL"]
                prompt = (
                    f"""You are an expert Lean 4 programmer assisting in autoformalization.
                    Your goal is to faithfully formalize a single step described in natural language by a student into *one single line* of valid Lean 4 tactic code.\n

                    Generate the single line of Lean 4 code for this step:\n
                    NL: {nl}\nFL: """
                )
                formatted_data.append({
                    "prompt": prompt,
                    "completion": f" {fl}",
                    "text": prompt + f" {fl}"
                })

    return Dataset.from_list(formatted_data)

def tokenize_function(examples, tokenizer):
    MAX_LENGTH = 512  # Adjust based on your model's context window
    
    # Process each prompt-completion pair
    result = {
        "input_ids": [],
        "attention_mask": [],
        "labels": []
    }
    
    for prompt, completion in zip(examples["prompt"], examples["completion"]):
        # Tokenize prompt and completion separately
        prompt_tokens = tokenizer.encode(prompt, add_special_tokens=False)
        completion_tokens = tokenizer.encode(completion, add_special_tokens=False)
        
        # Combine with appropriate truncation to fit within MAX_LENGTH
        if len(prompt_tokens) + len(completion_tokens) > MAX_LENGTH - 2:  # -2 for special tokens
            # Prioritize keeping the completion intact
            completion_length = min(len(completion_tokens), MAX_LENGTH // 2)
            prompt_length = MAX_LENGTH - 2 - completion_length
            
            prompt_tokens = prompt_tokens[-prompt_length:] if prompt_length > 0 else []
            completion_tokens = completion_tokens[:completion_length]
        
        # Add special tokens
        input_ids = [tokenizer.bos_token_id] + prompt_tokens + completion_tokens + [tokenizer.eos_token_id]
        
        # Create attention mask (1 for all tokens)
        attention_mask = [1] * len(input_ids)
        
        # Create labels: -100 for prompt, actual ids for completion
        labels = [-100] * (len(prompt_tokens) + 1) + completion_tokens + [tokenizer.eos_token_id]
        
        # Pad sequences to ensure fixed length
        padding_length = MAX_LENGTH - len(input_ids)
        if padding_length > 0:
            input_ids = input_ids + [tokenizer.pad_token_id] * padding_length
            attention_mask = attention_mask + [0] * padding_length
            labels = labels + [-100] * padding_length
        
        # Ensure all sequences have exactly MAX_LENGTH
        input_ids = input_ids[:MAX_LENGTH]
        attention_mask = attention_mask[:MAX_LENGTH]
        labels = labels[:MAX_LENGTH]
        
        # Ensure labels have the same length as input_ids
        if len(labels) != len(input_ids):
            # Adjust labels to match input_ids length
            if len(labels) < len(input_ids):
                labels = labels + [-100] * (len(input_ids) - len(labels))
            else:
                labels = labels[:len(input_ids)]
        
        # Sanity check to prevent errors
        assert len(input_ids) == len(attention_mask) == len(labels) == MAX_LENGTH
        
        result["input_ids"].append(input_ids)
        result["attention_mask"].append(attention_mask)
        result["labels"].append(labels)
    
    return result

def main():
    os.makedirs(OUTPUT_DIR, exist_ok=True)
    os.makedirs('plots', exist_ok=True)
    
    print("Loading training dataset...")
    train_dataset = prepare_dataset(TRAIN_DATASET_PATH)
    print(f"Training dataset loaded with {len(train_dataset)} examples")
    
    print("Loading validation dataset...")
    eval_dataset = prepare_dataset(VAL_DATASET_PATH)
    print(f"Validation dataset loaded with {len(eval_dataset)} examples")

    print("Loading tokenizer...")
    tokenizer = AutoTokenizer.from_pretrained(MODEL_NAME, token=HF_TOKEN)
    
    if tokenizer.pad_token is None:
        tokenizer.pad_token = tokenizer.eos_token
    
    print("Tokenizing datasets...")
    train_tokenized = train_dataset.map(
        lambda examples: tokenize_function(examples, tokenizer),
        batched=True,
        remove_columns=["prompt", "completion", "text"]
    )
    
    eval_tokenized = eval_dataset.map(
        lambda examples: tokenize_function(examples, tokenizer),
        batched=True,
        remove_columns=["prompt", "completion", "text"]
    )
    
    print("Loading model...")
    # model = AutoModelForCausalLM.from_pretrained(
    #     MODEL_NAME,
    #     torch_dtype=torch.float16,
    #     device_map="auto",
    #     token=HF_TOKEN
    # )

    bnb_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_compute_dtype=torch.float16,
    bnb_4bit_use_double_quant=True,
    bnb_4bit_quant_type="nf4",
)

    model = AutoModelForCausalLM.from_pretrained(
        MODEL_NAME,
        quantization_config=bnb_config,
        device_map="auto",  
        token=HF_TOKEN
    )


    print(f"Model is on device: {next(model.parameters()).device}")
    print("Preparing model for LoRA training...")
    # model = prepare_model_for_kbit_training(model)
    
    peft_config = LoraConfig(
        task_type=TaskType.CAUSAL_LM,
        inference_mode=False,
        r=LORA_R,
        lora_alpha=LORA_ALPHA,
        lora_dropout=LORA_DROPOUT,
        # query, key, value, linear layer in attn block
        target_modules=["q_proj", "k_proj", "v_proj", "o_proj"]
    )
    
    model = get_peft_model(model, peft_config)
    model.print_trainable_parameters()
    
    num_examples = len(train_tokenized)
    steps_per_epoch = num_examples // BATCH_SIZE
    total_steps = steps_per_epoch * EPOCHS
    warmup_steps = int(0.1 * total_steps)  
    
    print(f"Training for {EPOCHS} epochs with {steps_per_epoch} steps per epoch")
    print(f"Total steps: {total_steps}, with {warmup_steps} warmup steps")
    
    training_args = TrainingArguments(
        output_dir=OUTPUT_DIR,
        learning_rate=LEARNING_RATE,
        per_device_train_batch_size=BATCH_SIZE,
        per_device_eval_batch_size=BATCH_SIZE,
        num_train_epochs=EPOCHS,
        weight_decay=0.01,
        logging_dir=f"{OUTPUT_DIR}/logs",
        logging_steps=10,
        eval_strategy="epoch",
        save_strategy="epoch",
        save_total_limit=3,
        load_best_model_at_end=True,
        push_to_hub=False,
        lr_scheduler_type="cosine",  # Use cosine scheduler
        warmup_steps=warmup_steps,   # Set warmup steps
    )
    
    data_collator = DataCollatorForLanguageModeling(
        tokenizer=tokenizer,
        mlm=False
)
    
    loss_callback = LossCallback()
    
    trainer = Trainer(
        model=model,
        args=training_args,
        train_dataset=train_tokenized,
        eval_dataset=eval_tokenized,
        data_collator=data_collator,
        callbacks=[loss_callback]
    )
    
    print("Starting training...")
    trainer.train()
    

    print("Saving model...")
    trainer.save_model(f"{OUTPUT_DIR}/final")
    
    plt.figure(figsize=(10, 6))
    plt.plot(loss_callback.epochs, loss_callback.training_losses, 'b-', label='Training Loss')
    plt.plot(loss_callback.epochs, loss_callback.eval_losses, 'r-', label='Validation Loss')
    plt.xlabel('Epoch')
    plt.ylabel('Loss')
    plt.title('Training and Validation Loss')
    plt.legend()
    plt.grid(True)
    plt.savefig(f'{OUTPUT_DIR}/final_loss_plot.png')
    print(f"Final loss plot saved to {OUTPUT_DIR}/final_loss_plot.png")
    
    if loss_callback.learning_rates:
        steps, rates = zip(*loss_callback.learning_rates)
        
        plt.figure(figsize=(10, 6))
        plt.plot(steps, rates, 'g-')
        plt.xlabel('Step')
        plt.ylabel('Learning Rate')
        plt.title('Final Learning Rate Schedule (Cosine)')
        plt.grid(True)
        plt.savefig(f'{OUTPUT_DIR}/final_lr_plot.png')
        print(f"Final learning rate plot saved to {OUTPUT_DIR}/final_lr_plot.png")
    
    print("Training complete!")

if __name__ == "__main__":
    main()