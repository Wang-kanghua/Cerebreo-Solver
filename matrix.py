import json
import numpy as np
import requests
from pathlib import Path
from typing import List, Dict, Tuple

class ConcurrencyMatrixGenerator:
    def __init__(self, api_key, model="deepseek-chat"):
        self.api_key = api_key
        self.model = model
        self.api_url = "https://api.deepseek.com/v1/chat/completions"
    
    def read_file(self, file_path):
        """Read file content"""
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def extract_all_bins(self, bins_data):
        """Extract all bins from the coverage data"""
        all_bins = []
        bin_id_map = {}
        
        for testpoint in bins_data:
            for bin_item in testpoint.get('bins', []):
                bin_info = {
                    'bin_id': bin_item['bin_id'],
                    'testpoint_id': testpoint['testpoint_id'],
                    'description': bin_item['description'],
                    'spec_reference': bin_item.get('spec_reference', ''),
                    'signals_involved': bin_item.get('signals_involved', [])
                }
                all_bins.append(bin_info)
                bin_id_map[bin_item['bin_id']] = bin_info
        
        return all_bins, bin_id_map
    
    def create_concurrency_prompt(self, all_bins, spec_content, verilog_content):
        """Create structured prompt for concurrency analysis"""
        bins_info = "\n".join([
            f"Bin {i+1}: ID={bin['bin_id']}, Description='{bin['description']}', "
            f"Signals={bin.get('signals_involved', [])}, SpecRef={bin.get('spec_reference', 'N/A')}"
            for i, bin in enumerate(all_bins)
        ])
        
        prompt = f"""
# SCENARIOS CONCURRENCY MATRIX GENERATION TASK

## SPECIFICATION CONTENT:
{spec_content}

## DUT VERILOG CODE:
{verilog_content}

## COVERAGE BINS INFORMATION:
Total bins: {len(all_bins)}
{bins_info}

## INSTRUCTIONS:
Analyze pairwise concurrency relationships between all coverage bins. For each pair of bins (i, j), determine if they can be covered by the same stimulus (concurrent) or not (mutually exclusive).

### ANALYSIS CRITERIA:
1. **Semantic Compatibility**: Check if the functional scenarios described by the bins can logically occur together
2. **Signal Conflicts**: Identify conflicts in required signal values or states
3. **Mode Exclusivity**: Detect mutually exclusive operational modes
4. **Temporal Constraints**: Consider timing requirements and state sequencing
5. **Resource Conflicts**: Identify shared resources that cannot be accessed simultaneously

### CONCURRENCY RULES:
- Return TRUE if bins can be concurrent (same stimulus can cover both)
- Return FALSE if bins are mutually exclusive due to:
  * Contradictory register values
  * Mutually exclusive modes
  * Conflicting signal requirements
  * Temporal ordering constraints
  * Resource access conflicts

### OUTPUT REQUIREMENTS:
Generate a JSON object with:
1. concurrency_matrix: 2D boolean array where matrix[i][j] indicates concurrency between bin_i and bin_j
2. bin_ordering: List of bin IDs in the same order as matrix indices
3. conflict_reasons: Dictionary mapping bin pairs to reasons for non-concurrency (if any)

### OUTPUT FORMAT:
{{
  "concurrency_matrix": [
    [true, false, true, ...],
    [false, true, false, ...],
    ...
  ],
  "bin_ordering": ["BIN_T_1_1", "BIN_T_1_2", "BIN_T_2_1", ...],
  "conflict_reasons": {{
    "BIN_T_1_1-BIN_T_1_2": "Conflicting reset requirements",
    "BIN_T_1_1-BIN_T_2_1": "Mutually exclusive operational modes"
  }}
}}

Provide ONLY the JSON output without any additional text or explanation.
"""
        return prompt
    
    def call_deepseek_api(self, prompt):
        """Call DeepSeek API"""
        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json"
        }
        
        payload = {
            "model": self.model,
            "messages": [
                {
                    "role": "system",
                    "content": "You are an expert verification engineer specializing in concurrency analysis. You analyze coverage bins and determine pairwise concurrency relationships based on semantic compatibility, signal conflicts, mode exclusivity, and temporal constraints. You provide responses in exact JSON format without additional text."
                },
                {
                    "role": "user",
                    "content": prompt
                }
            ],
            "temperature": 0.1,
            "max_tokens": 4000
        }
        
        try:
            response = requests.post(self.api_url, headers=headers, json=payload, timeout=120)
            response.raise_for_status()
            return response.json()['choices'][0]['message']['content']
        except Exception as e:
            print(f"API call error: {e}")
            return None
    
    def validate_matrix(self, matrix, bin_ordering, all_bins):
        """Validate the concurrency matrix"""
        n = len(all_bins)
        
        # Check matrix dimensions
        if len(matrix) != n or any(len(row) != n for row in matrix):
            return False, "Matrix dimensions don't match number of bins"
        
        # Check bin ordering
        if len(bin_ordering) != n:
            return False, "Bin ordering length doesn't match number of bins"
        
        # Check matrix symmetry (should be symmetric)
        for i in range(n):
            for j in range(n):
                if matrix[i][j] != matrix[j][i]:
                    return False, f"Matrix not symmetric at ({i},{j}) vs ({j},{i})"
        
        # Check diagonal (bins should always be concurrent with themselves)
        for i in range(n):
            if not matrix[i][i]:
                return False, f"Bin {bin_ordering[i]} not concurrent with itself"
        
        return True, "Matrix validation passed"
    
    def generate_concurrency_matrix(self, bins_file, spec_file, verilog_file, output_file):
        """Generate concurrency matrix for all coverage bins"""
        # Read input files
        with open(bins_file, 'r', encoding='utf-8') as f:
            bins_data = json.load(f)
        
        spec_content = self.read_file(spec_file)
        verilog_content = self.read_file(verilog_file)
        
        # Extract all bins
        all_bins, bin_id_map = self.extract_all_bins(bins_data)
        
        if not all_bins:
            print("No bins found in the input file")
            return None
        
        print(f"Found {len(all_bins)} coverage bins for concurrency analysis...")
        
        # Create prompt
        prompt = self.create_concurrency_prompt(all_bins, spec_content, verilog_content)
        
        # Call API
        api_response = self.call_deepseek_api(prompt)
        
        if api_response:
            try:
                # Parse JSON response
                result = json.loads(api_response.strip())
                
                # Validate the result
                matrix = result.get('concurrency_matrix', [])
                bin_ordering = result.get('bin_ordering', [])
                conflict_reasons = result.get('conflict_reasons', {})
                
                # Validate matrix structure
                is_valid, validation_msg = self.validate_matrix(matrix, bin_ordering, all_bins)
                
                if not is_valid:
                    print(f"Matrix validation failed: {validation_msg}")
                    # Create fallback matrix (all concurrent)
                    n = len(all_bins)
                    fallback_matrix = [[True] * n for _ in range(n)]
                    bin_ordering_fallback = [bin['bin_id'] for bin in all_bins]
                    
                    result = {
                        "concurrency_matrix": fallback_matrix,
                        "bin_ordering": bin_ordering_fallback,
                        "conflict_reasons": {},
                        "validation_warning": validation_msg
                    }
                
                # Add metadata
                result["total_bins"] = len(all_bins)
                result["analysis_timestamp"] = "2024-01-01T00:00:00Z"  # Would use datetime.now() in production
                
                # Save results
                with open(output_file, 'w', encoding='utf-8') as f:
                    json.dump(result, f, indent=2, ensure_ascii=False)
                
                print(f"Concurrency matrix generated! Results saved to: {output_file}")
                
                # Print summary
                n = len(result['concurrency_matrix'])
                concurrent_pairs = sum(sum(row) for row in result['concurrency_matrix']) - n  # Subtract diagonal
                total_pairs = n * n - n  # Exclude diagonal
                concurrency_rate = concurrent_pairs / total_pairs if total_pairs > 0 else 0
                
                print(f"Matrix size: {n}x{n}")
                print(f"Concurrent pairs: {concurrent_pairs}/{total_pairs} ({concurrency_rate:.1%})")
                print(f"Conflict reasons documented: {len(result.get('conflict_reasons', {}))}")
                
                return result
                
            except json.JSONDecodeError as e:
                print(f"Failed to parse API response: {e}")
                print(f"Raw response: {api_response[:500]}...")
                return None
        else:
            print("API call failed")
            return None

# Usage example
if __name__ == "__main__":
    # Configuration
    DEEPSEEK_API_KEY = "your_deepseek_api_key_here"  # Replace with your API key
    
    # File paths
    BINS_FILE = "coverage_bins.json"  # Input from coverage bin generation
    SPEC_FILE = "spec.txt"
    VERILOG_FILE = "dut.v"
    OUTPUT_FILE = "concurrency_matrix.json"
    
    # Create concurrency analyzer instance
    analyzer = ConcurrencyMatrixGenerator(api_key=DEEPSEEK_API_KEY)
    
    # Generate concurrency matrix
    result = analyzer.generate_concurrency_matrix(
        bins_file=BINS_FILE,
        spec_file=SPEC_FILE,
        verilog_file=VERILOG_FILE,
        output_file=OUTPUT_FILE
    )
    
    if result:
        # Example of how to use the matrix
        matrix = result['concurrency_matrix']
        bin_ordering = result['bin_ordering']
        
        print("\nConcurrency Matrix Preview:")
        print("Bin Ordering:", bin_ordering)
        print("Matrix Shape:", len(matrix), "x", len(matrix[0]) if matrix else 0)
        
        # Show first few rows
        print("\nFirst 3 rows:")
        for i in range(min(3, len(matrix))):
            print(f"Row {i} ({bin_ordering[i]}): {matrix[i][:5]}...")
