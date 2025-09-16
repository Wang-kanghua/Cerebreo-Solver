import os
import re
import csv
from pathlib import Path

def extract_complete_assertion(lines, start_line_num):

    assertion_lines = []
    brace_count = 0
    parenthesis_count = 0
    bracket_count = 0
    in_assertion = False
    found_start = False
    max_search_lines = 100
    

    start_line = lines[start_line_num - 1].strip()
    

    is_immediate_assert = re.search(r'^\s*assert\s*\([^)]+\)\s*(begin|;|$)', start_line, re.IGNORECASE)
    is_property_decl = re.search(r'^\s*property\s+\w+\s*', start_line, re.IGNORECASE)
    is_sequence_decl = re.search(r'^\s*sequence\s+\w+\s*', start_line, re.IGNORECASE)
    is_directive = re.search(r'^\s*(assert|assume|cover|restrict)\b', start_line, re.IGNORECASE)
    
    for i in range(start_line_num - 1, min(start_line_num + max_search_lines, len(lines))):
        original_line = lines[i]
        line_clean = original_line.strip()
        
        if not in_assertion:

            if (re.match(r'^\s*(assert|assume|cover|restrict|property|sequence)\b', line_clean) or
                (i == start_line_num - 1 and (is_immediate_assert or is_property_decl or is_sequence_decl or is_directive))):
                in_assertion = True
                found_start = True
                assertion_lines.append(original_line)
                
                parenthesis_count += line_clean.count('(') - line_clean.count(')')
                brace_count += line_clean.count('{') - line_clean.count('}')
                bracket_count += line_clean.count('[') - line_clean.count(']')
                
 
                if (is_immediate_assert and not re.search(r'begin', line_clean, re.IGNORECASE) and
                    parenthesis_count == 0 and brace_count == 0 and bracket_count == 0 
                    and line_clean.endswith(';')):
                    break
                continue
        
        if in_assertion:
            assertion_lines.append(original_line)
            

            parenthesis_count += line_clean.count('(') - line_clean.count(')')
            brace_count += line_clean.count('{') - line_clean.count('}')
            bracket_count += line_clean.count('[') - line_clean.count(']')

            
            if is_immediate_assert and re.search(r'^\s*end\s*;?\s*$', line_clean, re.IGNORECASE):
                break
                
            if re.search(r'^\s*endproperty\s*(:\s*\w+)?\s*;?\s*$', line_clean, re.IGNORECASE):
                break
                
            if re.search(r'^\s*endsequence\s*(:\s*\w+)?\s*;?\s*$', line_clean, re.IGNORECASE):
                break
                
            if (parenthesis_count == 0 and brace_count == 0 and bracket_count == 0 
                and line_clean.endswith(';')):
                break
                
            if (i > start_line_num and 
                not line_clean and 
                not re.search(r'^\s*(assert|assume|cover|restrict|property|sequence)\b', 
                             lines[i+1].strip() if i+1 < len(lines) else '', re.IGNORECASE)):
                break
    
    if not found_start:
        return ""
    
    complete_code = ''.join(assertion_lines).rstrip()
    
    if (is_property_decl and 
        not re.search(r'endproperty', complete_code, re.IGNORECASE) and
        len(complete_code.split('\n')) < 10):
        return extract_extended_property(lines, start_line_num, complete_code)
    
    if (is_immediate_assert and 
        re.search(r'begin', complete_code, re.IGNORECASE) and
        not re.search(r'^\s*end\s*;?\s*$', complete_code.split('\n')[-1].strip(), re.IGNORECASE)):
        return extract_extended_immediate_assert(lines, start_line_num, complete_code)
    
    return complete_code

def extract_extended_property(lines, start_line_num, partial_code):

    max_extended_lines = 150
    extended_lines = partial_code.split('\n')
    found_end = False
    
    start_idx = start_line_num + len(extended_lines) - 1
    for i in range(start_idx, min(start_idx + max_extended_lines, len(lines))):
        line = lines[i]
        extended_lines.append(line)
        
        line_clean = line.strip()
        if re.search(r'^\s*endproperty\s*(:\s*\w+)?\s*;?\s*$', line_clean, re.IGNORECASE):
            found_end = True
            break
        
        if re.search(r'^\s*property\s+\w+\s*', line_clean, re.IGNORECASE):
            break
    
    result = '\n'.join(extended_lines).rstrip()
    
    if not found_end and not re.search(r'endproperty', result, re.IGNORECASE):
        return partial_code
    
    return result

def extract_extended_immediate_assert(lines, start_line_num, partial_code):

    max_extended_lines = 50
    extended_lines = partial_code.split('\n')
    found_end = False
    
    start_idx = start_line_num + len(extended_lines) - 1
    for i in range(start_idx, min(start_idx + max_extended_lines, len(lines))):
        line = lines[i]
        extended_lines.append(line)
        
        line_clean = line.strip()
        if re.search(r'^\s*end\s*;?\s*$', line_clean, re.IGNORECASE):
            found_end = True
            break
        
        if re.search(r'^\s*(assert|assume|cover|restrict)\b', line_clean, re.IGNORECASE):
            break
    
    result = '\n'.join(extended_lines).rstrip()
    
    if not found_end and not re.search(r'^\s*end\s*;?\s*$', result.split('\n')[-1].strip(), re.IGNORECASE):
        return partial_code
    
    return result

def is_verilog_assertion(line):

    line_clean = line.strip()
    
    if (not line_clean or 
        line_clean.startswith(('//', '/*', '*')) or
        re.match(r'^\s*`', line_clean) or
        re.match(r'^\s*#', line_clean)):
        return False
    
    line_clean = re.sub(r'//.*$', '', line_clean)
    line_clean = re.sub(r'/\*.*?\*/', '', line_clean)
    line_clean = line_clean.strip()
    
    assertion_patterns = [
        r'assert\s*\([^)]+\)\s*;',  # 匹配行中的任何assert语句
        
        r'^\s*property\s+\w+\s*',
        r'^\s*sequence\s+\w+\s*',
        r'^\s*endproperty\s*(:\s*\w+)?\s*;?\s*$',
        r'^\s*endsequence\s*(:\s*\w+)?\s*;?\s*$',
        
        r'^\s*(assert|assume|cover|restrict)\s*(property\s*)?\([^)]+\)\s*;',
        r'^\s*\w+\s*:\s*(assert|assume|cover|restrict)\s*(property\s*)?\([^)]+\)\s*;',
        r'^\s*(assert|assume|cover)\s+property\s*\([^)]+\)\s*;',
        
        r'^\s*endproperty\s*:\s*\w+\s*;?\s*$',
        r'^\s*endsequence\s*:\s*\w+\s*;?\s*$',
        
        r'^\s*end\s*;?\s*$',
        
        r'^\s*@\(.*\)',
        r'^\s*disable\s+iff',
        r'^\s*\|->',
        r'^\s*\|=>',
        r'^\s*##\d',
    ]
    
    for pattern in assertion_patterns:
        if re.search(pattern, line_clean, re.IGNORECASE):
            return True
    
    return False

def split_multiple_assertions(line):
    """
    分割一行中的多个断言语句
    例如: "assert (a); assert (b);" -> ["assert (a);", "assert (b);"]
    """
    assertions = []
    current_assertion = ""
    parenthesis_count = 0
    brace_count = 0
    bracket_count = 0
    
    tokens = re.split(r'(\s+|\(|\)|\{|\}|\[|\]|;)', line)
    
    for token in tokens:
        current_assertion += token
        
        parenthesis_count += token.count('(') - token.count(')')
        brace_count += token.count('{') - token.count('}')
        bracket_count += token.count('[') - token.count(']')
        
        if (token.strip() == ';' and 
            parenthesis_count == 0 and brace_count == 0 and bracket_count == 0 and
            re.search(r'assert\s*\(', current_assertion, re.IGNORECASE)):
            assertions.append(current_assertion.strip())
            current_assertion = ""
    
    if current_assertion.strip() and re.search(r'assert\s*\(', current_assertion, re.IGNORECASE):
        assertions.append(current_assertion.strip())
    
    return assertions

def classify_assertion_type(assertion_code):

    clean_code = re.sub(r'//.*?$|/\*.*?\*/', '', assertion_code, flags=re.DOTALL)
    clean_code = re.sub(r'\s+', ' ', clean_code).strip()
    
    if re.search(r'assert\s*\([^)]+\)\s*(;|begin|$)', clean_code, re.IGNORECASE):
        return "immediate_assert"
    elif re.search(r'^\s*property\s+\w+\s*', clean_code, re.IGNORECASE):
        return "property_declaration"
    elif re.search(r'^\s*sequence\s+\w+\s*', clean_code, re.IGNORECASE):
        return "sequence_declaration"
    elif re.search(r'^\s*assert\s+property\s*\(', clean_code, re.IGNORECASE):
        return "assert_property"
    elif re.search(r'^\s*assume\s+property\s*\(', clean_code, re.IGNORECASE):
        return "assume_property"
    elif re.search(r'^\s*cover\s+property\s*\(', clean_code, re.IGNORECASE):
        return "cover_property"
    elif re.search(r'^\s*restrict\s+property\s*\(', clean_code, re.IGNORECASE):
        return "restrict_property"
    else:
        return "unknown"

def find_assertion_files(directory):

    file_stats = {}
    assertion_details = []
    processed_lines = set()
    seen_assertions = set()  
    base_path = Path(directory)
    sv_files = list(base_path.rglob('*.sv'))
    v_files = list(base_path.rglob('*.v'))
    verilog_files = sv_files + v_files
    

    
    for file_idx, file_path in enumerate(verilog_files, 1):
        if not file_path.is_file():
            continue
        
        if file_idx % 100 == 0:
            print(f"已处理 {file_idx}/{len(verilog_files)} 个文件...")
            
        assertion_count = 0
        file_assertions = []
        file_processed_lines = set()
        
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
            
            for line_num, line in enumerate(lines, 1):
                if line_num in file_processed_lines:
                    continue
                    
                if is_verilog_assertion(line):

                    multiple_assertions = split_multiple_assertions(line)
                    
                    if multiple_assertions and len(multiple_assertions) > 1:

                        for i, assertion in enumerate(multiple_assertions):
                            if assertion and assertion not in seen_assertions:
                                seen_assertions.add(assertion)
                                assertion_count += 1
                                
                                assertion_type = classify_assertion_type(assertion)
                                
                                file_assertions.append({
                                    'line_number': line_num,
                                    'code': assertion,
                                    'line_count': 1,
                                    'type': assertion_type
                                })
                                
                                assertion_details.append({
                                    'file_name': file_path.name,
                                    'file_path': str(file_path),
                                    'line_number': line_num,
                                    'assertion_code': assertion,
                                    'line_count': 1,
                                    'assertion_type': assertion_type
                                })
                    else:

                        complete_assertion = extract_complete_assertion(lines, line_num)
                        if complete_assertion and complete_assertion not in seen_assertions:
                            seen_assertions.add(complete_assertion)
                            assertion_count += 1
                            
                            assertion_line_count = len(complete_assertion.split('\n'))
                            for i in range(line_num, line_num + assertion_line_count):
                                file_processed_lines.add(i)
                            
                            assertion_type = classify_assertion_type(complete_assertion)
                            
                            file_assertions.append({
                                'line_number': line_num,
                                'code': complete_assertion,
                                'line_count': assertion_line_count,
                                'type': assertion_type
                            })
                            
                            assertion_details.append({
                                'file_name': file_path.name,
                                'file_path': str(file_path),
                                'line_number': line_num,
                                'assertion_code': complete_assertion,
                                'line_count': assertion_line_count,
                                'assertion_type': assertion_type
                            })

            if assertion_count > 0:
                file_stats[str(file_path)] = {
                    'file_name': file_path.name,
                    'assertion_count': assertion_count,
                    'file_path': str(file_path),
                    'assertions': file_assertions
                }

        except (IOError, UnicodeDecodeError, PermissionError) as e:
            print(f"警告：无法读取文件 {file_path}: {str(e)}")
            continue

    return file_stats, assertion_details


def test_always_block_assertions():

    test_code = """always_ff @( posedge clk ) begin
    if ( !reset ) begin
      assert ( ^in_val  !== 1'bx );
      assert ( ^val_S1  !== 1'bx );
      assert ( ^val_S2  !== 1'bx );
      assert ( ^val_S3  !== 1'bx );
      assert ( ^out_val !== 1'bx );
    end
  end
"""
    
    lines = test_code.split('\n')
    print("always块中的断言测试:")
    for i, line in enumerate(lines, 1):
        if is_verilog_assertion(line):
            print(f"第{i}行检测到断言: {line.strip()}")
            assertions = split_multiple_assertions(line)
            if len(assertions) > 1:
                print(f"  包含多个断言: {assertions}")
            else:
                print(f"  单个断言: {assertions[0] if assertions else '无'}")

def main():

    test_always_block_assertions()
    
    target_directory = ""
    output_csv = ""
    details_csv = ""
    stats_csv = ""

    if not os.path.isdir(target_directory):
        print(f"错误：目录 {target_directory} 不存在！")
        return

    print(f"正在搜索目录: {target_directory}...")
    file_stats, assertion_details = find_assertion_files(target_directory)

    # 保存各种格式的结果
    save_to_csv(file_stats, output_csv)
    save_assertion_details(assertion_details, details_csv)
    save_type_statistics(assertion_details, stats_csv)
    
    # 输出统计信息
    total_files = len(file_stats)
    total_assertions = sum(stats['assertion_count'] for stats in file_stats.values())
    
    print(f"\n处理完成！")
    print(f"结果文件:")
    print(f"  - 文件统计: {output_csv}")
    print(f"  - 详细断言: {details_csv}")
    print(f"  - 类型统计: {stats_csv}")
    
    # 输出类型统计
    type_stats = {}
    for detail in assertion_details:
        a_type = detail['assertion_type']
        type_stats[a_type] = type_stats.get(a_type, 0) + 1
    
    print(f"\n断言类型分布:")
    for a_type, count in sorted(type_stats.items(), key=lambda x: x[1], reverse=True):
        percentage = (count / total_assertions * 100) if total_assertions > 0 else 0
        print(f"  {a_type}: {count} ({percentage:.1f}%)")
    
    # 显示立即断言示例
    immediate_examples = [d for d in assertion_details if d['assertion_type'] == 'immediate_assert']
    if immediate_examples:
        print(f"\n立即断言示例 (前5个):")
        for i, example in enumerate(immediate_examples[:5], 1):
            print(f"{i}. {example['assertion_code']}")

if __name__ == "__main__":
    main()
