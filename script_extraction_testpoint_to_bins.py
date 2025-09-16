import json
import re
import requests
from pathlib import Path

class DeepSeekTestpointAnalyzer:
    def __init__(self, api_key, model="..."):
        self.api_key = api_key
        self.model = model
        self.api_url = "..."
        
    def read_file(self, file_path):
        with open(file_path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def extract_interface_signals(self, verilog_code):
        signals = []
        
        module_pattern = r'module\s+\w+\s*\((.*?)\);.*?endmodule'
        ports_pattern = r'(input|output|inout)\s+(reg|wire)?\s*(\[.*?\])?\s*(\w+)'
        
        module_match = re.search(module_pattern, verilog_code, re.DOTALL)
        if module_match:
            ports_section = module_match.group(1)
            port_declarations = re.findall(ports_pattern, ports_section)
            for direction, _, width, signal_name in port_declarations:
                signal_info = {
                    'name': signal_name,
                    'direction': direction,
                    'width': width if width else "1-bit"
                }
                signals.append(signal_info)
        
        return signals
    
    def create_structured_prompt(self, spec_content, interface_signals, testpoint_desc):
        prompt = f"""
# SPECIFICATION ANALYSIS TASK

## SPECIFICATION CONTENT:
{spec_content}

## DUT INTERFACE SIGNALS:
{json.dumps(interface_signals, indent=2)}

## TESTPOINT DESCRIPTION:
{testpoint_desc}

## INSTRUCTIONS:
1. Analyze the testpoint description in context of the SPECIFICATION
2. Correlate with DUT interface signals where applicable
3. Decompose into functional coverage bins
4. For each bin, provide:
   - Unique hierarchical identifier (BIN_Ti_j format)
   - Clear natural language description
   - Reference to relevant SPEC section (if applicable)
   - Associated interface signals (if applicable)

## OUTPUT FORMAT (JSON):
{{
  "testpoint_id": "T_i",
  "bins": [
    {{
      "bin_id": "BIN_T_i_j",
      "description": "detailed bin description",
      "spec_reference": "relevant spec section",
      "signals_involved": ["signal1", "signal2"]
    }}
  ]
}}

Please provide ONLY the JSON output without any additional text.
"""
        return prompt
    
    def call_deepseek_api(self, prompt):
        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json"
        }
        
        payload = {
            "model": self.model,
            "messages": [
                {
                    "role": "system",
                    "content": "You are an expert verification engineer specialized in testpoint analysis and coverage bin decomposition. Provide precise, technical responses in the requested JSON format."
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
            response = requests.post(self.api_url, headers=headers, json=payload, timeout=60)
            response.raise_for_status()
            return response.json()['choices'][0]['message']['content']
        except Exception as e:
            print(f"API ERROR: {e}")
            return None
    
    def parse_testpoints(self, testpoints_file, spec_file, verilog_file, output_file):

        with open(testpoints_file, 'r', encoding='utf-8') as f:
            testpoints = json.load(f)
        
        spec_content = self.read_file(spec_file)
        verilog_content = self.read_file(verilog_file)
        
  
        interface_signals = self.extract_interface_signals(verilog_content)
        
        results = []
        
        for i, testpoint in enumerate(testpoints, 1):
            testpoint_id = f"T_{i}"
            testpoint_desc = testpoint.get('description', '') if isinstance(testpoint, dict) else str(testpoint)
            
            print(f"analyze {testpoint_id}...")
            

            prompt = self.create_structured_prompt(
                spec_content, 
                interface_signals, 
                testpoint_desc
            )

            api_response = self.call_deepseek_api(prompt)
            
            if api_response:
                try:

                    result_data = json.loads(api_response.strip())
                    result_data['testpoint_id'] = testpoint_id
                    results.append(result_data)
                    print(f"成功解析测试点 {testpoint_id}")
                except json.JSONDecodeError:
                    print(f"Error: {api_response}")
 
                    results.append({
                        "testpoint_id": testpoint_id,
                        "bins": [],
                        "error": "Failed to parse API response"
                    })
            else:
                results.append({
                    "testpoint_id": testpoint_id,
                    "bins": [],
                    "error": "API call failed"
                })
        

        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        
        print(f"complete!sace as: {output_file}")
        return results


if __name__ == "__main__":

    DEEPSEEK_API_KEY = "..."      

    TESTPOINTS_FILE = "testpoints.json"
    SPEC_FILE = "spec.txt"
    VERILOG_FILE = "dut.v"
    OUTPUT_FILE = "coverage_bins.json"
    
    analyzer = DeepSeekTestpointAnalyzer(api_key=DEEPSEEK_API_KEY)
    

    results = analyzer.parse_testpoints(
        testpoints_file=TESTPOINTS_FILE,
        spec_file=SPEC_FILE,
        verilog_file=VERILOG_FILE,
        output_file=OUTPUT_FILE
    )
    
    # 打印摘要
    total_bins = sum(len(result.get('bins', [])) for result in results)
    print(f"sum bins: {total_bins} ")
