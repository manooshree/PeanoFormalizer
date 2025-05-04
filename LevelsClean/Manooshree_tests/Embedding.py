# embeddings.py
import json
from sentence_transformers import SentenceTransformer
import numpy as np
from typing import List, Dict
import argparse
from pathlib import Path
from sklearn.metrics.pairwise import cosine_similarity
import os

os.environ["TOKENIZERS_PARALLELISM"] = "false"

class ProofEmbedder:
    def __init__(self):
        #print("Initializing SentenceTransformer model...")
        self.model = SentenceTransformer('all-MiniLM-L6-v2')  
        self.embeddings = None
        self.theorem_data = None
        #print("Model initialized!")

    def process_json_file(self, filepath: str, output_path: str):
        """Process JSON file containing theorem data and create embeddings."""
        #print(f"\nReading JSON file: {filepath}")
        try:
            with open(filepath, 'r') as f:
                theorems = json.load(f)
            #print(f"Successfully loaded {len(theorems)} theorems")
        except Exception as e:
            #print(f"Error reading JSON file: {e}")
            return
        
        filtered_theorems = []
        for theorem in theorems:
            # Skip if the NL starts with these markers
            if (not theorem['NL'].startswith('--Proof Statement:') and 
                not theorem['NL'].startswith('theorem') and
                not 'Proof Statement:' in theorem['NL']):
                filtered_theorems.append(theorem)

        # Extract NL statements
        nl_statements = [theorem['NL'] for theorem in filtered_theorems]
        #print(f"Extracted {len(nl_statements)} NL statements")

        #print("\nCreating embeddings...")
        # Create embeddings for NL statements
        embeddings = self.model.encode(nl_statements, show_progress_bar=True)

        # Store embeddings and theorem data
        self.embeddings = embeddings
        self.theorem_data = theorems

        # Save embeddings and theorem data
        output_data = {
            'embeddings': embeddings.tolist(),
            'theorems': theorems  
        }

        #print(f"\nSaving embeddings and theorem data to {output_path}")
        try:
            with open(output_path, 'w') as f:
                json.dump(output_data, f)
            #print("Successfully saved embeddings and theorem data!")
        except Exception as e:
            #print(f"Error saving embeddings: {e}")
            return

    def load_embeddings(self, filepath: str):
        """Load pre-computed embeddings and theorem data from file."""
        #print(f"\nLoading embeddings from {filepath}")
        try:
            with open(filepath, 'r') as f:
                data = json.load(f)
            self.embeddings = np.array(data['embeddings'])
            self.theorem_data = data['theorems']
            #print(f"Successfully loaded embeddings for {len(self.theorem_data)} theorems")
        except Exception as e:
            #print(f"Error loading embeddings: {e}")
            return

    def retrieve_similar_steps(self, query: str, n: int = 5) -> List[Dict]:
        if self.embeddings is None or self.theorem_data is None:
            raise ValueError("No embeddings loaded. Please process a file or load embeddings first.")
            
        # Create embedding for the query
        #print("Creating embedding for query...")
        query_embedding = self.model.encode([query])
        
        # Calculate cosine similarities
        #print("Finding similar theorems...")
        similarities = cosine_similarity(query_embedding, self.embeddings)[0]
        
        # Get top n similar indices
        top_n_indices = np.argsort(similarities)[-n:][::-1]
        
        # Create result list
        results = []
        for idx in top_n_indices:
            results.append({
                'similarity': float(similarities[idx]),
                **self.theorem_data[idx]
            })
            
        #print(f"Found {len(results)} similar theorems!")
        return results

def main():
    parser = argparse.ArgumentParser(description='Create embeddings for theorem proofs')
    parser.add_argument('input_file', help='Path to input JSON file')
    parser.add_argument('output_file', help='Path to save embeddings')
    
    args = parser.parse_args()
    
    embedder = ProofEmbedder()
    embedder.process_json_file(args.input_file, args.output_file)

if __name__ == "__main__":
    main()