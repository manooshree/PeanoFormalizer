import json
import torch
import torch.nn.functional as F
from sentence_transformers import SentenceTransformer, util
import os

os.environ["TOKENIZERS_PARALLELISM"] = "true"

def lean_rag(query_statement, embedding_path, file_path, top_k=5):
    model = SentenceTransformer('paraphrase-MPNet-base-v2')
    # Force CPU device for consistency
    device = torch.device('cpu')
    query_embedding = model.encode(query_statement, convert_to_tensor=True).to(device)
    with open(file_path, 'r') as file:
        data = json.load(file)
    data = [item for item in data if not item['FL'].startswith('theorem')]
    try:
        nl_embeddings = torch.load(embedding_path, map_location=torch.device('cpu'))
    except FileNotFoundError:
        print("Creating new embeddings...")
        model = SentenceTransformer('paraphrase-MPNet-base-v2')
        nl_statements = [item['NL'] for item in data if 'NL' in item]
        nl_embeddings = model.encode(nl_statements, convert_to_tensor=True)
        torch.save(nl_embeddings, embedding_path)
    
    nl_embeddings_cpu = nl_embeddings.to(device)
    
    cosine_similarities = F.cosine_similarity(query_embedding, nl_embeddings_cpu)
    top_k = torch.topk(cosine_similarities, top_k)
    return [data[i]['FL'] for i in top_k.indices]

if __name__ == "__main__":
    statement = "Prove that zero is not equal to one"
    print(f"\nQuery: {statement}\n")
    print("Top 10 similar proofs:")
    lean_rag(statement)