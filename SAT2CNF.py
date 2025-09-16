import re
from typing import Dict, List, Tuple, Set
import itertools

class TseitinTransformer:
    def __init__(self):
        self.variable_counter = 1  # Start from 1 (0 is reserved)
        self.clauses = []
        self.variable_map = {}  # Maps original expressions to new variables
        self.original_vars = set()
        
    def get_fresh_variable(self):
        """Generate a fresh variable"""
        var_id = self.variable_counter
        self.variable_counter += 1
        return var_id
    
    def extract_variables(self, expression: str) -> Set[str]:
        """Extract all variable names from expression"""
        # Remove operators and parentheses, then split
        cleaned = re.sub(r'[&|!()\-><=\s]+', ' ', expression)
        variables = set([var for var in cleaned.split() if var and not var.isdigit()])
        return variables
    
    def parse_expression(self, expression: str) -> Tuple:
        """Parse logical expression into AST-like structure"""
        expression = expression.replace(' ', '')
        
        # Handle parentheses
        if expression.startswith('(') and expression.endswith(')'):
            return self.parse_expression(expression[1:-1])
        
        # Find the main operator (outside parentheses)
        paren_level = 0
        operators = ['->', '|', '&', '!']
        
        for i in range(len(expression) - 1, -1, -1):
            char = expression[i]
            if char == ')':
                paren_level += 1
            elif char == '(':
                paren_level -= 1
            elif paren_level == 0:
                # Check for multi-character operators
                if i > 0 and expression[i-1:i+1] == '->':
                    return ('->', 
                           self.parse_expression(expression[:i-1]),
                           self.parse_expression(expression[i+1:]))
                # Check for single-character operators
                elif char in ['|', '&']:
                    return (char, 
                           self.parse_expression(expression[:i]),
                           self.parse_expression(expression[i+1:]))
        
        # Handle negation
        if expression.startswith('!'):
            return ('!', self.parse_expression(expression[1:]))
        
        # Base case: variable or constant
        if expression in ['0', '1']:
            return expression
        else:
            self.original_vars.add(expression)
            return expression
    
    def transform_expression(self, ast) -> int:
        """Recursively transform AST using Tseitin transformation"""
        if isinstance(ast, str):
            # Variable or constant
            if ast in self.variable_map:
                return self.variable_map[ast]
            elif ast in ['0', '1']:
                # Handle constants
                var_id = self.get_fresh_variable()
                self.variable_map[ast] = var_id
                if ast == '0':
                    self.clauses.append([-var_id])  # ¬var (must be false)
                else:
                    self.clauses.append([var_id])   # var (must be true)
                return var_id
            else:
                # Regular variable
                if ast not in self.variable_map:
                    self.variable_map[ast] = self.get_fresh_variable()
                return self.variable_map[ast]
        
        operator = ast[0]
        
        if operator == '!':
            # Negation: ¬A
            operand = self.transform_expression(ast[1])
            result_var = self.get_fresh_variable()
            
            # Add clauses: (result_var ∨ A) ∧ (¬result_var ∨ ¬A)
            self.clauses.append([result_var, operand])          # result_var ∨ A
            self.clauses.append([-result_var, -operand])        # ¬result_var ∨ ¬A
            
            return result_var
        
        elif operator == '&':
            # Conjunction: A ∧ B
            left = self.transform_expression(ast[1])
            right = self.transform_expression(ast[2])
            result_var = self.get_fresh_variable()
            
            # Add clauses: 
            # (¬result_var ∨ A) ∧ (¬result_var ∨ B) ∧ (result_var ∨ ¬A ∨ ¬B)
            self.clauses.append([-result_var, left])            # ¬result_var ∨ A
            self.clauses.append([-result_var, right])           # ¬result_var ∨ B
            self.clauses.append([result_var, -left, -right])    # result_var ∨ ¬A ∨ ¬B
            
            return result_var
        
        elif operator == '|':
            # Disjunction: A ∨ B
            left = self.transform_expression(ast[1])
            right = self.transform_expression(ast[2])
            result_var = self.get_fresh_variable()
            
            # Add clauses:
            # (result_var ∨ ¬A) ∧ (result_var ∨ ¬B) ∧ (¬result_var ∨ A ∨ B)
            self.clauses.append([result_var, -left])            # result_var ∨ ¬A
            self.clauses.append([result_var, -right])           # result_var ∨ ¬B
            self.clauses.append([-result_var, left, right])     # ¬result_var ∨ A ∨ B
            
            return result_var
        
        elif operator == '->':
            # Implication: A → B ≡ ¬A ∨ B
            left = self.transform_expression(ast[1])
            right = self.transform_expression(ast[2])
            result_var = self.get_fresh_variable()
            
            # Transform implication to disjunction: A → B ≡ ¬A ∨ B
            # Then handle as disjunction
            not_left = self.get_fresh_variable()
            
            # Add negation of left
            self.clauses.append([not_left, left])               # not_left ∨ A
            self.clauses.append([-not_left, -left])             # ¬not_left ∨ ¬A
            
            # Handle disjunction: not_left ∨ right
            self.clauses.append([result_var, -not_left])        # result_var ∨ ¬not_left
            self.clauses.append([result_var, -right])           # result_var ∨ ¬right
            self.clauses.append([-result_var, not_left, right]) # ¬result_var ∨ not_left ∨ right
            
            return result_var
        
        else:
            raise ValueError(f"Unknown operator: {operator}")
    
    def to_cnf(self, sat_expression: str) -> Dict:
        """Convert SAT expression to CNF using Tseitin transformation"""
        # Reset state for new transformation
        self.clauses = []
        self.variable_map = {}
        self.original_vars = set()
        self.variable_counter = 1
        
        # Extract original variables
        original_variables = self.extract_variables(sat_expression)
        
        # Parse and transform
        ast = self.parse_expression(sat_expression)
        root_var = self.transform_expression(ast)
        
        # Add the root variable as a unit clause (must be true)
        self.clauses.append([root_var])
        
        # Create variable mapping
        var_mapping = {}
        reverse_mapping = {}
        
        # Map original variables
        for var in original_variables:
            if var in self.variable_map:
                var_mapping[var] = self.variable_map[var]
                reverse_mapping[self.variable_map[var]] = var
        
        # Map auxiliary variables
        for i in range(1, self.variable_counter):
            if i not in reverse_mapping:
                reverse_mapping[i] = f"aux_{i}"
        
        # Remove duplicate clauses and sort literals within clauses
        unique_clauses = set()
        final_clauses = []
        
        for clause in self.clauses:
            # Sort and remove duplicates within clause
            sorted_clause = sorted(set(clause), key=lambda x: (abs(x), x < 0))
            clause_tuple = tuple(sorted_clause)
            if clause_tuple not in unique_clauses:
                unique_clauses.add(clause_tuple)
                final_clauses.append(sorted_clause)
        
        return {
            'cnf_clauses': final_clauses,
            'variable_mapping': var_mapping,
            'reverse_mapping': reverse_mapping,
            'num_variables': self.variable_counter - 1,
            'num_clauses': len(final_clauses),
            'original_expression': sat_expression
        }
    
    def cnf_to_dimacs(self, cnf_result: Dict) -> str:
        """Convert CNF result to DIMACS format"""
        clauses = cnf_result['cnf_clauses']
        num_vars = cnf_result['num_variables']
        num_clauses = cnf_result['num_clauses']
        
        dimacs = f"p cnf {num_vars} {num_clauses}\n"
        
        for clause in clauses:
            dimacs += " ".join(map(str, clause)) + " 0\n"
        
        return dimacs
    
    def pretty_print_cnf(self, cnf_result: Dict) -> str:
        """Pretty print CNF result in human-readable format"""
        output = []
        output.append(f"Original expression: {cnf_result['original_expression']}")
        output.append(f"Number of variables: {cnf_result['num_variables']}")
        output.append(f"Number of clauses: {cnf_result['num_clauses']}")
        output.append("")
        
        output.append("Variable mapping:")
        for orig_var, cnf_var in cnf_result['variable_mapping'].items():
            output.append(f"  {orig_var} -> {cnf_var}")
        
        output.append("")
        output.append("CNF clauses:")
        for i, clause in enumerate(cnf_result['cnf_clauses'], 1):
            clause_str = " ∨ ".join([
                f"¬{cnf_result['reverse_mapping'][abs(lit)]}" if lit < 0 
                else f"{cnf_result['reverse_mapping'][abs(lit)]}"
                for lit in clause
            ])
            output.append(f"Clause {i}: {clause_str}")
        
        return "\n".join(output)

# Example usage and test function
def test_tseitin_transformation():
    """Test the Tseitin transformation with example expressions"""
    transformer = TseitinTransformer()
    
    test_expressions = [
        "A & B",                    # Simple AND
        "A | B",                    # Simple OR
        "!(A & B)",                 # NAND
        "A -> B",                   # Implication
        "(A | B) & (C | D)",        # Complex expression
        "A & !A",                   # Contradiction
        "A | !A",                   # Tautology
    ]
    
    for expr in test_expressions:
        print(f"\n{'='*50}")
        print(f"Transforming: {expr}")
        print(f"{'='*50}")
        
        try:
            result = transformer.to_cnf(expr)
            print(transformer.pretty_print_cnf(result))
            
            # Also show DIMACS format
            print("\nDIMACS format:")
            print(transformer.cnf_to_dimacs(result))
            
        except Exception as e:
            print(f"Error transforming {expr}: {e}")

# Batch processing function for SAT expressions from JSON
def process_sat_expressions_to_cnf(input_file: str, output_file: str):
    """Process multiple SAT expressions from JSON file to CNF"""
    with open(input_file, 'r', encoding='utf-8') as f:
        sat_data = json.load(f)
    
    transformer = TseitinTransformer()
    results = []
    
    for item in sat_data:
        if 'sat_expression' in item and not item['sat_expression'].startswith('ERROR'):
            try:
                print(f"Processing: {item.get('bin_id', 'unknown')}")
                cnf_result = transformer.to_cnf(item['sat_expression'])
                
                result_entry = {
                    'testpoint_id': item.get('testpoint_id'),
                    'bin_id': item.get('bin_id'),
                    'original_sat': item['sat_expression'],
                    'cnf_result': cnf_result,
                    'dimacs_format': transformer.cnf_to_dimacs(cnf_result)
                }
                results.append(result_entry)
                
            except Exception as e:
                print(f"Error processing {item.get('bin_id', 'unknown')}: {e}")
                results.append({
                    'testpoint_id': item.get('testpoint_id'),
                    'bin_id': item.get('bin_id'),
                    'error': str(e),
                    'original_sat': item.get('sat_expression', '')
                })
        else:
            results.append({
                'testpoint_id': item.get('testpoint_id'),
                'bin_id': item.get('bin_id'),
                'error': 'Invalid SAT expression',
                'original_sat': item.get('sat_expression', '')
            })
    
    # Save results
    with open(output_file, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    
    print(f"CNF transformation completed! Results saved to {output_file}")
    return results

if __name__ == "__main__":
    import json
    
    # Test with individual expressions
    print("Testing Tseitin transformation with example expressions:")
    test_tseitin_transformation()
    
    # Example of batch processing (uncomment to use)
    # process_sat_expressions_to_cnf('sat_expressions.json', 'cnf_results.json')
