import json
import re
import requests
from pathlib import Path

class DeepSeekSATGenerator:
    def __init__(self, api_key, model="deepseek-chat"):
        self.api_key = api_key
        self.model = model
        self.api_url = "https://api.deepseek.com/v1/chat/completions"
    
    def create_sat_prompt(self, bin_data, spec_content, interface_signals):
        """Create structured prompt for SAT expression generation"""
        prompt = f"""
# SAT EXPRESSION GENERATION TASK

## SPECIFICATION CONTENT:
{spec_content}

## DUT INTERFACE SIGNALS:
{json.dumps(interface_signals, indent=2)}

## COVERAGE BIN INFORMATION:
- Testpoint ID: {bin_data['testpoint_id']}
- Bin ID: {bin_data['bin_id']}
- Bin Description: {bin_data['description']}
- Spec Reference: {bin_data.get('spec_reference', 'N/A')}
- Signals Involved: {bin_data.get('signals_involved', [])}

## INSTRUCTIONS:
Systematically translate the natural language coverage bin into formal SAT logic expressions through step-by-step analysis:

1. STATE ANALYSIS:
   - Classify the scenario as single-state or multi-state
   - Define state variables required for temporal modeling if needed
   - Identify all relevant signals and their roles

2. PROPOSITIONAL LOGIC GENERATION:
   - Create precise logic expressions using ONLY signal/state variables
   - Use standard operators: AND (&), OR (|), NOT (!), IMPLIES (->)
   - Expand all implications into equivalent AND/OR/NOT expressions
   - Ensure expressions are syntactically correct for SAT solvers

3. MULTI-STATE HANDLING (if applicable):
   - For temporal scenarios, define state transitions
   - Use appropriate temporal operators or state sequencing
   - Conjoin clauses across states to form final SAT instance

4. OUTPUT REQUIREMENTS:
   - Provide exactly one SAT expression per coverage bin
   - Maintain bijective mapping: BIN_T_i_j ↔ SAT_T_i_j
   - Use only the identified signals and operators
   - Ensure the expression captures the complete verification condition

## OPERATOR DEFINITIONS:
- AND: &
- OR: | 
- NOT: !
- IMPLIES: -> (must be expanded to equivalent AND/OR/NOT)
- Parentheses: () for grouping

## OUTPUT FORMAT (JSON):
{{
  "testpoint_id": "{bin_data['testpoint_id']}",
  "bin_id": "{bin_data['bin_id']}",
  "sat_expression": "formal_SAT_expression_here",
  "state_analysis": "single-state|multi-state",
  "signals_used": ["signal1", "signal2"],
  "logic_steps": [
    "step 1 description",
    "step 2 description"
  ]
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
                    "content": "You are an expert formal verification engineer specialized in SAT expression generation. You systematically analyze coverage bins and produce precise, syntactically correct SAT expressions using only allowed operators and signals. You provide responses in exact JSON format without additional text."
                },
                {
                    "role": "user",
                    "content": prompt
                }
            ],
            "temperature": 0.1,
            "max_tokens": 2000
        }
        
        try:
            response = requests.post(self.api_url, headers=headers, json=payload, timeout=90)
            response.raise_for_status()
            return response.json()['choices'][0]['message']['content']
        except Exception as e:
            print(f"API call error: {e}")
            return None

    def extract_interface_signals(self, verilog_content):
        """Extract interface signals from Verilog code"""
        signals = []
        module_pattern = r'module\s+\w+\s*\((.*?)\);.*?endmodule'
        ports_pattern = r'(input|output|inout)\s+(reg|wire)?\s*(\[.*?\])?\s*(\w+)'
        
        module_match = re.search(module_pattern, verilog_content, re.DOTALL)
        if module_match:
            ports_section = module_match.group(1)
            port_declarations = re.findall(ports_pattern, ports_section)
            for direction, _, width, signal_name in port_declarations:
                signals.append(signal_name)
        
        return list(set(signals))  # Remove duplicates

    def validate_sat_expression(self, expression, allowed_signals):
        """Basic validation of SAT expression syntax"""
        # Check for invalid operators (placeholder - would need more robust validation)
        invalid_ops = ['&&', '||', '==', '!=']
        for op in invalid_ops:
            if op in expression:
                return False, f"Invalid operator detected: {op}"
        
        # Check for unknown signals (basic check)
        words = re.findall(r'\b[a-zA-Z_][a-zA-Z0-9_]*\b', expression)
        for word in words:
            if word.lower() not in ['and', 'or', 'not', 'implies'] and word not in allowed_signals:
                return False, f"Unknown signal detected: {word}"
        
        return True, "Expression appears valid"

    def generate_sat_expressions(self, bins_file, spec_file, verilog_file, output_file):
        """Generate SAT expressions for all coverage bins"""
        # Read input files
        with open(bins_file, 'r', encoding='utf-8') as f:
            coverage_bins = json.load(f)
        
        spec_content = Path(spec_file).read_text(encoding='utf-8')
        verilog_content = Path(verilog_file).read_text(encoding='utf-8')
        
        # Extract interface signals
        interface_signals = self.extract_interface_signals(verilog_content)
        
        results = []
        
        for testpoint_data in coverage_bins:
            testpoint_id = testpoint_data['testpoint_id']
            bins = testpoint_data.get('bins', [])
            
            print(f"Processing testpoint {testpoint_id} with {len(bins)} bins...")
            
            for bin_data in bins:
                bin_id = bin_data['bin_id']
                print(f"  Generating SAT for {bin_id}...")
                
                # Create prompt for this bin
                prompt = self.create_sat_prompt({
                    'testpoint_id': testpoint_id,
                    'bin_id': bin_id,
                    'description': bin_data['description'],
                    'spec_reference': bin_data.get('spec_reference', ''),
                    'signals_involved': bin_data.get('signals_involved', [])
                }, spec_content, interface_signals)
                
                # Call API
                api_response = self.call_deepseek_api(prompt)
                
                if api_response:
                    try:
                        # Parse JSON response
                        sat_result = json.loads(api_response.strip())
                        
                        # Basic validation
                        allowed_signals = interface_signals + bin_data.get('signals_involved', [])
                        is_valid, validation_msg = self.validate_sat_expression(
                            sat_result['sat_expression'], allowed_signals
                        )
                        
                        if not is_valid:
                            sat_result['validation_warning'] = validation_msg
                        
                        results.append(sat_result)
                        print(f"    ✓ SAT generated for {bin_id}")
                        
                    except json.JSONDecodeError as e:
                        print(f"    ✗ Failed to parse API response for {bin_id}: {e}")
                        results.append({
                            "testpoint_id": testpoint_id,
                            "bin_id": bin_id,
                            "sat_expression": "ERROR: Failed to generate SAT",
                            "error": "JSON parse error",
                            "raw_response": api_response[:200] + "..." if len(api_response) > 200 else api_response
                        })
                else:
                    print(f"    ✗ API call failed for {bin_id}")
                    results.append({
                        "testpoint_id": testpoint_id,
                        "bin_id": bin_id,
                        "sat_expression": "ERROR: API call failed",
                        "error": "API call failed"
                    })
        
        # Save results
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        
        print(f"SAT generation completed! Results saved to: {output_file}")
        return results

# Usage example
if __name__ == "__main__":
    # Configuration
    DEEPSEEK_API_KEY = "your_deepseek_api_key_here"  # Replace with your API key
    
    # File paths
    BINS_FILE = "coverage_bins.json"  # Input from previous step
    SPEC_FILE = "spec.txt"
    VERILOG_FILE = "dut.v"
    OUTPUT_FILE = "sat_expressions.json"
    
    # Create SAT generator instance
    sat_generator = DeepSeekSATGenerator(api_key=DEEPSEEK_API_KEY)
    
    # Generate SAT expressions
    results = sat_generator.generate_sat_expressions(
        bins_file=BINS_FILE,
        spec_file=SPEC_FILE,
        verilog_file=VERILOG_FILE,
        output_file=OUTPUT_FILE
    )
    
    # Print summary
    successful = sum(1 for r in results if not r.get('error') and 'ERROR' not in r.get('sat_expression', ''))
    print(f"Successfully generated SAT expressions for {successful}/{len(results)} bins")
