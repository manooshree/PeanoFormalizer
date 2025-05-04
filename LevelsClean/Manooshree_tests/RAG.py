
from .Embedding import ProofEmbedder

# def RAG(query: str, embeddings_file: str, n: int = 5) -> list:
#     """
#     Retrieve similar proof steps for a given query.
    
#     Args:
#         query (str): The query to search for
#         embeddings_file (str): Path to the embeddings JSON file
#         n (int): Number of results to return
        
#     Returns:
#         list: List of similar proof steps, each containing NL and FL
#     """
#     # Initialize embedder and load embeddings
#     embedder = ProofEmbedder()
#     embedder.load_embeddings(embeddings_file)
    
#     # Get similar steps
#     similar_steps = embedder.retrieve_similar_steps(query, n=n)
    
#     # Format results
#     results = []
#     for step in similar_steps:
#         results.append({
#             'NL': step['NL'],
#             'FL': step['FL']
#         })
    
#     return results

# if __name__ == "__main__":
#     # Example usage
#     query = "Apply the associative property of addition"
#     results = RAG(query, 'Addition.json')
    
#     #print(f"Query: {query}")
#     #for result in results:
#         #print(f"\nNL: {result['NL']}")
#         #print(f"FL: {result['FL']}")


#NEW STARTS HERE
def RAG(query: str, embeddings_file: str, n: int = 5) -> str:
    """
    Retrieve similar proof steps for a given query.
    
    Args:
        query (str): The query to search for
        embeddings_file (str): Path to the embeddings JSON file
        n (int): Number of results to return
        
    Returns:
        str: Formatted string of similar proof steps
    """
    # Initialize embedder and load embeddings
    embedder = ProofEmbedder()
    embedder.load_embeddings(embeddings_file)
    
    # Get similar steps
    similar_steps = embedder.retrieve_similar_steps(query, n=n)
    
    # Format results as a string
    output = []
    for step in similar_steps:
        output.append(f"NL: {step['NL']}")
        output.append(f"FL: {step['FL']}")
        output.append(f"Similarity: {step.get('similarity', 0):.3f}")
        output.append("")  # Add blank line between entries
    
    return "\n".join(output)