
#key: 
import pandas as pd
import requests
import json
import os
import time
from pathlib import Path

class AssertionAnalyzer:
    def __init__(self, api_key, api_url="https://api.deepseek.com/v1/chat/completions"):
        self.api_key = api_key
        self.api_url = api_url
        self.headers = {
            "Authorization": f"Bearer {api_key}",
            "Content-Type": "application/json"
        }

    def read_verilog_file(self, file_path):
        """Read Verilog/SystemVerilog file content"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                return f.read()
        except FileNotFoundError:
            print(f"File not found: {file_path}")
            return None
        except Exception as e:
            print(f"Error reading file {file_path}: {e}")
            return None

    def call_deepseek_api(self, verilog_code, assertion_code):
        """Call DeepSeek API to generate English description"""
        prompt = f"""
Please analyze the functionality of the following assertion in Verilog/SystemVerilog code and provide a detailed English description:

Complete Verilog/SystemVerilog code:

    {verilog_code}

Specific assertion code to analyze:

    {assertion_code}

Provide a clear technical description that:

1.States the specific condition being monitored
2.Explains the purpose of this check
3.Uses simple but precise technical language

Format: A single, compact technical description ready for use as code documentation.
"""
        
        payload = {
            "model": "deepseek-coder",
            "messages": [
                {"role": "system", "content": "You are a professional digital circuit verification engineer specializing in analyzing Verilog/SystemVerilog assertions. Provide clear, technical English descriptions."},
                {"role": "user", "content": prompt}
            ],
            "temperature": 0.1,
            "max_tokens": 2000
        }
        
        try:
            print("  Calling DeepSeek API...")
            response = requests.post(self.api_url, headers=self.headers, json=payload, timeout=60)
            response.raise_for_status()
            result = response.json()
            description = result['choices'][0]['message']['content'].strip()
            print("  API call successful")
            return description
        except Exception as e:
            print(f"  API Error: {e}")
            return f"API Error: {str(e)}"
    
    def process_csv(self, csv_file, output_file, delay=2.0):
        """Process CSV file with assertions"""
        try:

            df = pd.read_csv(csv_file, delimiter=',')
            print(f"Successfully loaded {len(df)} rows")
            print(f"Columns: {df.columns.tolist()}")
            
        except Exception as e:
            print(f"Error reading CSV file: {e}")
            return
        
        results = []
        
        for index, row in df.iloc[5500:].iterrows():
            print(f"\n=== Processing row {index + 1}/{len(df)} ===")
            
            try:
                file_path = row['file_path']
                assertion_code = row['assertion_code']
                file_name = row['file_name']
                line_number = row['line_number']
                
                print(f"  File: {file_name}")
                print(f"  Path: {file_path}")
                print(f"  Line: {line_number}")
                print(f"  Assertion: {assertion_code[:100]}...")
                

                if not os.path.exists(file_path):
                    print(f"  ✗ ERROR: File does not exist")
                    results.append({
                        'file_name': file_name,
                        'file_path': file_path,
                        'line_number': line_number,
                        'assertion_code': assertion_code,
                        'description': 'ERROR: File not found'
                    })
                    continue
                

                verilog_code = self.read_verilog_file(file_path)
                if verilog_code is None:
                    results.append({
                        'file_name': file_name,
                        'file_path': file_path,
                        'line_number': line_number,
                        'assertion_code': assertion_code,
                        'description': 'ERROR: Cannot read file'
                    })
                    continue
                
                print(f"File read successfully ({len(verilog_code)} chars)")
                

                description = self.call_deepseek_api(verilog_code, assertion_code)
                
                results.append({
                    'file_name': file_name,
                    'file_path': file_path,
                    'line_number': line_number,
                    'assertion_code': assertion_code,
                    'description': description
                })
                
                print(f"Description generated: {description[:100]}...")
                

                output_df = pd.DataFrame(results)
                output_df.to_csv(output_file, index=False, sep=',') 
                print(f"Progress saved to: {output_file}")
                

                time.sleep(delay)
                
            except Exception as e:
                print(f"ERROR processing row: {e}")
                continue
        
        print(f"\n Processing completed! Final results saved to: {output_file}")
        

        success_count = sum(1 for r in results if not str(r['description']).startswith('ERROR'))
        error_count = len(results) - success_count
        print(f"Summary: {success_count} successful, {error_count} errors")

def main():
    # Configuration
    API_KEY = "" #
    INPUT_CSV = ""  # 输入CSV文件
    OUTPUT_CSV = ""  # 输出文件
    

    if API_KEY == "your_deepseek_api_key_here":
        print("ERROR: Please replace 'your_deepseek_api_key_here' with your actual DeepSeek API key")
        return
    

    if not os.path.exists(INPUT_CSV):
        print(f"ERROR: Input file '{INPUT_CSV}' not found")
        return
    

    analyzer = AssertionAnalyzer(API_KEY)
    

    print("Starting assertion analysis...")
    analyzer.process_csv(INPUT_CSV, OUTPUT_CSV)

if __name__ == "__main__":
    main()
