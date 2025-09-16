import json
import numpy as np
from typing import List, Set, Dict, Tuple
from collections import defaultdict

class MaximalCliqueEnumerator:
    def __init__(self):
        self.cliques = []
        
    def load_concurrency_matrix(self, matrix_file: str) -> Tuple[np.ndarray, List[str]]:
        """Load concurrency matrix from JSON file"""
        with open(matrix_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        matrix = np.array(data['concurrency_matrix'], dtype=bool)
        bin_ordering = data['bin_ordering']
        
        # Verify matrix is symmetric
        if not np.array_equal(matrix, matrix.T):
            raise ValueError("Concurrency matrix is not symmetric")
        
        # Verify diagonal is all True (bins are compatible with themselves)
        if not np.all(np.diag(matrix)):
            raise ValueError("Diagonal elements should all be True")
        
        return matrix, bin_ordering
    
    def build_compatibility_graph(self, matrix: np.ndarray, bin_ordering: List[str]) -> Dict:
        """Build compatibility graph from concurrency matrix"""
        n = len(bin_ordering)
        graph = defaultdict(set)
        degrees = defaultdict(int)
        
        for i in range(n):
            for j in range(i + 1, n):  # Only consider upper triangle
                if matrix[i][j]:  # Bins are compatible
                    bin_i = bin_ordering[i]
                    bin_j = bin_ordering[j]
                    graph[bin_i].add(bin_j)
                    graph[bin_j].add(bin_i)
                    degrees[bin_i] += 1
                    degrees[bin_j] += 1
        
        # Add self-loops (each bin is compatible with itself)
        for bin_id in bin_ordering:
            graph[bin_id].add(bin_id)
            if bin_id not in degrees:
                degrees[bin_id] = 0
        
        return dict(graph), dict(degrees)
    
    def bron_kerbosch(self, R: Set, P: Set, X: Set, graph: Dict) -> None:
        """
        Standard Bron-Kerbosch algorithm for maximal clique enumeration
        
        Parameters:
        R: Current clique being built
        P: Candidate vertices that can extend the clique
        X: Vertices that have already been considered
        graph: Compatibility graph
        """
        if len(P) == 0 and len(X) == 0:
            # Found a maximal clique
            self.cliques.append(set(R))
            return
        
        # Choose pivot vertex to minimize recursion
        pivot = next(iter(P.union(X))) if P.union(X) else None
        if pivot:
            # Consider vertices not in the neighborhood of pivot
            candidates = P - graph[pivot]
        else:
            candidates = P
        
        for v in list(candidates):
            # Recursively extend clique with v
            neighbors_v = graph[v]
            self.bron_kerbosch(
                R.union({v}),
                P.intersection(neighbors_v),
                X.intersection(neighbors_v),
                graph
            )
            
            # Move v from P to X
            P.remove(v)
            X.add(v)
    
    def enhanced_bron_kerbosch(self, graph: Dict, degrees: Dict) -> List[Set]:
        """
        Enhanced Bron-Kerbosch algorithm with vertex removal strategy
        
        Parameters:
        graph: Compatibility graph
        degrees: Degree of each vertex
        
        Returns:
        List of maximal cliques
        """
        self.cliques = []
        
        # Step 1: Identify isolated vertices (degree 0, only self-compatible)
        all_vertices = set(graph.keys())
        isolated_vertices = {v for v, deg in degrees.items() if deg == 0}
        
        # Each isolated vertex forms a singleton maximal clique
        for v in isolated_vertices:
            self.cliques.append({v})
        
        # Step 2: Process remaining graph with enhanced algorithm
        remaining_vertices = all_vertices - isolated_vertices
        processed_vertices = set()
        
        while remaining_vertices:
            # Choose vertex with minimum degree for better efficiency
            v = min(remaining_vertices, key=lambda x: len(graph[x] & remaining_vertices))
            
            # Find maximal clique containing v
            neighbors_v = graph[v]
            R = {v}
            P = neighbors_v.intersection(remaining_vertices)
            X = set()
            
            # Use standard Bron-Kerbosch to find maximal clique containing v
            clique_containing_v = set()
            self.find_clique_containing_v(R, P, X, graph, remaining_vertices, clique_containing_v)
            
            if clique_containing_v:
                self.cliques.append(clique_containing_v)
                # Remove all vertices in this clique from further consideration
                remaining_vertices -= clique_containing_v
                processed_vertices.update(clique_containing_v)
            else:
                # Should not happen, but if it does, remove just this vertex
                remaining_vertices.remove(v)
                processed_vertices.add(v)
        
        return self.cliques
    
    def find_clique_containing_v(self, R: Set, P: Set, X: Set, graph: Dict, 
                               valid_vertices: Set, result: Set) -> bool:
        """
        Modified Bron-Kerbosch to find one maximal clique containing specific vertex
        """
        if len(P) == 0 and len(X) == 0:
            result.update(R)
            return True
        
        # Only consider valid vertices
        P = P.intersection(valid_vertices)
        X = X.intersection(valid_vertices)
        
        if len(P) == 0 and len(X) == 0:
            result.update(R)
            return True
        
        # Choose pivot to minimize recursion
        pivot = next(iter(P.union(X))) if P.union(X) else None
        if pivot:
            candidates = P - graph[pivot]
        else:
            candidates = P
        
        for u in list(candidates):
            neighbors_u = graph[u]
            found = self.find_clique_containing_v(
                R.union({u}),
                P.intersection(neighbors_u),
                X.intersection(neighbors_u),
                graph,
                valid_vertices,
                result
            )
            if found:
                return True
            
            P.remove(u)
            X.add(u)
        
        return False
    
    def validate_cliques(self, cliques: List[Set], graph: Dict) -> bool:
        """Validate that all cliques are maximal and correct"""
        all_vertices = set(graph.keys())
        covered_vertices = set()
        
        for clique in cliques:
            # Check clique is complete
            for u in clique:
                for v in clique:
                    if u != v and v not in graph[u]:
                        return False
            
            covered_vertices.update(clique)
        
        # Check all vertices are covered exactly once
        if covered_vertices != all_vertices:
            return False
        
        # Check cliques are maximal (no larger clique exists containing this one)
        for clique in cliques:
            for vertex in all_vertices - clique:
                if all(vertex in graph[u] for u in clique):
                    # This vertex is connected to all clique members
                    return False
        
        return True
    
    def find_maximal_cliques(self, matrix_file: str, output_file: str) -> Dict:
        """Main function to find all maximal cliques"""
        # Load and process data
        matrix, bin_ordering = self.load_concurrency_matrix(matrix_file)
        graph, degrees = self.build_compatibility_graph(matrix, bin_ordering)
        
        # Find maximal cliques using enhanced algorithm
        maximal_cliques = self.enhanced_bron_kerbosch(graph, degrees)
        
        # Validate results
        is_valid = self.validate_cliques(maximal_cliques, graph)
        if not is_valid:
            print("Warning: Clique validation failed. Using standard Bron-Kerbosch as fallback.")
            # Fallback to standard algorithm
            self.cliques = []
            all_vertices = set(graph.keys())
            self.bron_kerbosch(set(), all_vertices, set(), graph)
            maximal_cliques = self.cliques
        
        # Convert sets to sorted lists for JSON serialization
        clique_list = [sorted(list(clique)) for clique in maximal_cliques]
        
        # Prepare results
        results = {
            "maximal_cliques": clique_list,
            "total_cliques": len(clique_list),
            "total_bins": len(bin_ordering),
            "clique_sizes": [len(clique) for clique in clique_list],
            "validation_passed": is_valid,
            "bin_ordering": bin_ordering
        }
        
        # Calculate statistics
        if clique_list:
            results["max_clique_size"] = max(len(clique) for clique in clique_list)
            results["min_clique_size"] = min(len(clique) for clique in clique_list)
            results["avg_clique_size"] = sum(len(clique) for clique in clique_list) / len(clique_list)
        
        # Save results
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        
        print(f"Found {len(clique_list)} maximal cliques")
        print(f"Clique sizes: {results['clique_sizes']}")
        print(f"Results saved to: {output_file}")
        
        return results

# Example usage
if __name__ == "__main__":
    # Configuration
    MATRIX_FILE = "concurrency_matrix.json"  # Input from previous step
    OUTPUT_FILE = "maximal_cliques.json"
    
    # Create enumerator instance
    enumerator = MaximalCliqueEnumerator()
    
    # Find maximal cliques
    results = enumerator.find_maximal_cliques(MATRIX_FILE, OUTPUT_FILE)
    
    # Print summary
    print(f"\nSummary:")
    print(f"Total bins: {results['total_bins']}")
    print(f"Total maximal cliques: {results['total_cliques']}")
    print(f"Max clique size: {results.get('max_clique_size', 0)}")
    print(f"Min clique size: {results.get('min_clique_size', 0)}")
    print(f"Avg clique size: {results.get('avg_clique_size', 0):.2f}")
    print(f"Validation passed: {results['validation_passed']}")
    
    # Show first few cliques
    print(f"\nFirst 5 cliques:")
    for i, clique in enumerate(results['maximal_cliques'][:5]):
        print(f"Clique {i+1}: {clique}")
