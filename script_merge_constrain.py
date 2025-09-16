import json
import re
from typing import List, Dict, Set, Tuple, Optional
from collections import defaultdict

class TemporalConstraintMerger:
    def __init__(self):
        self.variable_scope = set()
        self.temporal_relationships = []
        self.merged_constraints = []
        self.clock_cycles_needed = 1
        self.instruction_variables = set()
        
    def extract_variables(self, sat_expression: str) -> Set[str]:
        pattern = r'[a-zA-Z_][a-zA-Z0-9_]*(\[\d+(:\d+)?\])?'
        variables = set()
        
        for match in re.finditer(pattern, sat_expression):
            var_name = match.group()
            if not any(op in var_name for op in ['&', '|', '!', '==', '!=']) and not var_name.replace('_', '').isdigit():
                variables.add(var_name)
        
        return variables
    
    def analyze_temporal_scope(self, variables: Set[str]) -> Dict:
        analysis = {
            'has_prev_instruction': False,
            'has_instruction': False,
            'has_other_temporal': False,
            'temporal_variables': set(),
            'instruction_variables': set()
        }
        
        for var in variables:
            if var.startswith('prev_instruction'):
                analysis['has_prev_instruction'] = True
                analysis['temporal_variables'].add(var)
                analysis['instruction_variables'].add(var)
            elif var.startswith('instruction'):
                analysis['has_instruction'] = True
                analysis['temporal_variables'].add(var)
                analysis['instruction_variables'].add(var)
            elif any(keyword in var for keyword in ['prev_', 'next_', 'cycle_', 'time_']):
                analysis['has_other_temporal'] = True
                analysis['temporal_variables'].add(var)
        
        return analysis
    
    def detect_temporal_dependencies(self, sat_expression: str) -> List[Dict]:
        dependencies = []
        
        raw_patterns = [
            r'instruction\[19:15\]\s*==\s*prev_instruction\[11:7\]',  # rs1 = prev_rd
            r'instruction\[24:20\]\s*==\s*prev_instruction\[11:7\]',  # rs2 = prev_rd
            r'prev_instruction\[19:15\]\s*==\s*instruction\[11:7\]',  # prev_rs1 = rd
            r'prev_instruction\[24:20\]\s*==\s*instruction\[11:7\]',  # prev_rs2 = rd
        ]
        
        for pattern in raw_patterns:
            if re.search(pattern, sat_expression):
                dep_type = "RAW" if "prev_instruction[11:7]" in pattern else "WAR"
                dependencies.append({
                    'type': dep_type,
                    'pattern': pattern,
                    'description': f"Register dependency between consecutive instructions"
                })
        
        temporal_patterns = [
            (r'prev_instruction.*instruction', "Instruction sequence constraint"),
            (r'cycle_\d+', "Multi-cycle timing constraint"),
            (r'time_\d+', "Timing constraint"),
        ]
        
        for pattern, description in temporal_patterns:
            if re.search(pattern, sat_expression):
                dependencies.append({
                    'type': "TIMING",
                    'pattern': pattern,
                    'description': description
                })
        
        return dependencies
    
    def normalize_constraint(self, sat_expression: str, cycle_offset: int = 0) -> str:
        if cycle_offset == 0:
            return sat_expression
        

        normalized = sat_expression
        
        if cycle_offset > 0:
            normalized = re.sub(r'prev_instruction', f'instruction_{cycle_offset-1}', normalized)
            normalized = re.sub(r'instruction(?![_\d])', f'instruction_{cycle_offset}', normalized)
        elif cycle_offset < 0:
            normalized = re.sub(r'instruction_(\d+)', lambda m: f'instruction_{int(m.group(1)) + cycle_offset}', normalized)
        
        return normalized
    
    def determine_clock_cycles(self, constraints: List[str]) -> int:
        max_cycle = 0
        
        for constraint in constraints:
            variables = self.extract_variables(constraint)
            analysis = self.analyze_temporal_scope(variables)
            
            if analysis['has_prev_instruction']:
                max_cycle = max(max_cycle, 2)
            
            cycle_vars = [var for var in variables if re.match(r'instruction_\d+', var) or re.match(r'cycle_\d+', var)]
            for var in cycle_vars:
                if match := re.search(r'(\d+)', var):
                    cycle_num = int(match.group(1))
                    max_cycle = max(max_cycle, cycle_num + 1)
        
        return max(1, max_cycle)
    
    def merge_constraints(self, constraints: List[str]) -> str:
        self.clock_cycles_needed = self.determine_clock_cycles(constraints)
        
        merged_parts = []
        
        for i, constraint in enumerate(constraints):

            variables = self.extract_variables(constraint)
            analysis = self.analyze_temporal_scope(variables)
            dependencies = self.detect_temporal_dependencies(constraint)
            
            self.variable_scope.update(variables)
            self.temporal_relationships.extend(dependencies)
            self.instruction_variables.update(analysis['instruction_variables'])

            normalized_constraint = self.normalize_constraint(constraint)
            merged_parts.append(f"({normalized_constraint})")
        

        merged_sat = " & ".join(merged_parts)
        
        return merged_sat
    
    def get_temporal_analysis(self) -> Dict:
        return {
            'clock_cycles_needed': self.clock_cycles_needed,
            'variable_scope': list(self.variable_scope),
            'temporal_relationships': self.temporal_relationships,
            'instruction_variables': list(self.instruction_variables)
        }

class SATConstraintProcessor:
    def __init__(self):
        self.merger = TemporalConstraintMerger()
    
    def load_constraints_from_json(self, json_file: str) -> List[str]:

        with open(json_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        constraints = []
        

        if isinstance(data, list):
            for item in data:
                if isinstance(item, dict) and 'sat_expression' in item:
                    constraints.append(item['sat_expression'])
                elif isinstance(item, str):
                    constraints.append(item)
        elif isinstance(data, dict):
            if 'constraints' in data:
                constraints = data['constraints']
            elif 'bins' in data:
                for bin_data in data['bins']:
                    if 'sat_expression' in bin_data:
                        constraints.append(bin_data['sat_expression'])
        
        return constraints
    
    def process_constraints(self, constraints: List[str]) -> Dict:

        merged_sat = self.merger.merge_constraints(constraints)
        analysis = self.merger.get_temporal_analysis()
        
        return {
            'merged_sat_expression': merged_sat,
            'temporal_analysis': analysis,
            'original_constraints_count': len(constraints)
        }
    
    def process_json_file(self, input_json: str, output_json: str = None) -> Dict:

        constraints = self.load_constraints_from_json(input_json)
        result = self.process_constraints(constraints)
        
        if output_json:
            with open(output_json, 'w', encoding='utf-8') as f:
                json.dump(result, f, indent=2, ensure_ascii=False)
            print(f"save as {output_json}")
        
        return result

###################EXAMPLE############################
def create_example_json():

    example_data = [
        {
            "bin_id": "BIN_T1_1",
            "description": "Execute ADD operation",
            "sat_expression": "(instruction[6:0] == 0b0110011) & (instruction[14:12] == 0b000) & (instruction[31:25] == 0b0000000) & (instruction[11:7] != 0)"
        },
        {
            "bin_id": "BIN_T6_ADD_1", 
            "description": "RAW hazard with previous ADD",
            "sat_expression": "(prev_instruction[6:0] == 0b0110011) & (prev_instruction[14:12] == 0b000) & (prev_instruction[31:25] == 0b0000000) & (prev_instruction[11:7] != 0) & (instruction[19:15] == prev_instruction[11:7])"
        },
        {
            "bin_id": "BIN_T7_ADD_ADD",
            "description": "ADD after ADD with RAW",
            "sat_expression": "(prev_instruction[6:0] == 0b0110011) & (prev_instruction[14:12] == 0b000) & (prev_instruction[31:25] == 0b0000000) & (prev_instruction[11:7] != 0) & (instruction[6:0] == 0b0110011) & (instruction[14:12] == 0b000) & (instruction[31:25] == 0b0000000) & (instruction[19:15] == prev_instruction[11:7])"
        }
    ]
    
    with open('example_constraints.json', 'w', encoding='utf-8') as f:
        json.dump(example_data, f, indent=2, ensure_ascii=False)
    
    return 'example_constraints.json'

def main():
    example_file = create_example_json()
    processor = SATConstraintProcessor()
    result = processor.process_json_file(example_file, 'merged_constraints.json')
    
    print("=" * 60)
    print("results")
    print("=" * 60)
    print(f"original_constraints_count: {result['original_constraints_count']}")
    print(f"clock: {result['temporal_analysis']['clock_cycles_needed']}")
    print(f"variable_scope: {len(result['temporal_analysis']['variable_scope'])}")
    
    print("\ntemporal_relationships:")
    for rel in result['temporal_analysis']['temporal_relationships']:
        print(f"  - {rel['type']}: {rel['description']}")
    
    print("\nmerged_SAT:")
    print(result['merged_sat_expression'])

if __name__ == "__main__":
    main()
