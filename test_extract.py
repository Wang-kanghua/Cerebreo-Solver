import os
import re
import csv
from pathlib import Path

def extract_complete_assertion(lines, start_line_num):
    """
    从起始行开始提取完整的断言语句，支持完整的property/sequence块
    """
    assertion_lines = []
    brace_count = 0
    parenthesis_count = 0
    bracket_count = 0
    in_assertion = False
    found_start = False
    max_search_lines = 100  # 增加搜索范围以处理复杂的property
    
    # 首先确定起始行的类型
    start_line = lines[start_line_num - 1].strip()
    
    # 检查是否是property/sequence声明开始
    is_property_decl = re.search(r'^\s*property\s+\w+\s*', start_line, re.IGNORECASE)
    is_sequence_decl = re.search(r'^\s*sequence\s+\w+\s*', start_line, re.IGNORECASE)
    is_directive = re.search(r'^\s*(assert|assume|cover|restrict)\b', start_line, re.IGNORECASE)
    
    for i in range(start_line_num - 1, min(start_line_num + max_search_lines, len(lines))):
        original_line = lines[i]
        line_clean = original_line.strip()
        
        if not in_assertion:
            # 匹配各种断言开始模式
            if (re.match(r'^\s*(assert|assume|cover|restrict|property|sequence)\b', line_clean) or
                (i == start_line_num - 1 and (is_property_decl or is_sequence_decl or is_directive))):
                in_assertion = True
                found_start = True
                assertion_lines.append(original_line)
                
                # 初始计数
                parenthesis_count += line_clean.count('(') - line_clean.count(')')
                brace_count += line_clean.count('{') - line_clean.count('}')
                bracket_count += line_clean.count('[') - line_clean.count(']')
                
                # 如果是单行断言且以分号结束
                if (parenthesis_count == 0 and brace_count == 0 and bracket_count == 0 
                    and line_clean.endswith(';')):
                    break
                continue
        
        if in_assertion:
            assertion_lines.append(original_line)
            
            # 更新括号计数
            parenthesis_count += line_clean.count('(') - line_clean.count(')')
            brace_count += line_clean.count('{') - line_clean.count('}')
            bracket_count += line_clean.count('[') - line_clean.count(']')
            
            # 检查结束条件
            
            # 1. 完整的property块结束（带或不带标签）
            if re.search(r'^\s*endproperty\s*(:\s*\w+)?\s*;?\s*$', line_clean, re.IGNORECASE):
                break
                
            # 2. 完整的sequence块结束
            if re.search(r'^\s*endsequence\s*(:\s*\w+)?\s*;?\s*$', line_clean, re.IGNORECASE):
                break
                
            # 3. 单行断言以分号结束且所有括号匹配
            if (parenthesis_count == 0 and brace_count == 0 and bracket_count == 0 
                and line_clean.endswith(';')):
                break
                
            # 4. 空行后的非断言内容（针对某些特殊情况）
            if (i > start_line_num and 
                not line_clean and 
                not re.search(r'^\s*(assert|assume|cover|restrict|property|sequence)\b', 
                             lines[i+1].strip() if i+1 < len(lines) else '', re.IGNORECASE)):
                break
    
    if not found_start:
        return ""
    
    complete_code = ''.join(assertion_lines).rstrip()
    
    # 验证提取的完整性 - 如果是property但没有找到endproperty，尝试扩展搜索
    if (is_property_decl and 
        not re.search(r'endproperty', complete_code, re.IGNORECASE) and
        len(complete_code.split('\n')) < 10):  # 如果提取的行数太少
        return extract_extended_property(lines, start_line_num, complete_code)
    
    return complete_code

def extract_extended_property(lines, start_line_num, partial_code):
    """
    处理未完整提取的property块，扩展搜索范围
    """
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
        
        # 如果遇到新的property开始，说明前一个没有正确结束
        if re.search(r'^\s*property\s+\w+\s*', line_clean, re.IGNORECASE):
            break
    
    result = '\n'.join(extended_lines).rstrip()
    
    # 如果还是没有找到endproperty，返回原始部分代码
    if not found_end and not re.search(r'endproperty', result, re.IGNORECASE):
        return partial_code
    
    return result

def is_verilog_assertion(line):
    """
    精确检测Verilog断言，包括property/sequence声明
    """
    line_clean = line.strip()
    
    # 跳过空行、注释和预处理指令
    if (not line_clean or 
        line_clean.startswith(('//', '/*', '*')) or
        re.match(r'^\s*`', line_clean) or
        re.match(r'^\s*#', line_clean)):
        return False
    
    # 移除行内注释
    line_clean = re.sub(r'//.*$', '', line_clean)
    line_clean = re.sub(r'/\*.*?\*/', '', line_clean)
    line_clean = line_clean.strip()
    
    # 检查真正的断言语法
    assertion_patterns = [
        # property/sequence 声明
        r'^\s*property\s+\w+\s*',
        r'^\s*sequence\s+\w+\s*',
        r'^\s*endproperty\s*(:\s*\w+)?\s*;?\s*$',
        r'^\s*endsequence\s*(:\s*\w+)?\s*;?\s*$',
        
        # 断言指令
        r'^\s*(assert|assume|cover|restrict)\s*(property\s*)?\([^)]+\)\s*;',
        r'^\s*\w+\s*:\s*(assert|assume|cover|restrict)\s*(property\s*)?\([^)]+\)\s*;',
        r'^\s*(assert|assume|cover)\s+property\s*\([^)]+\)\s*;',
        r'^\s*assert\s*\([^)]+\)\s*;',
        
        # 带标签的property/sequence结束
        r'^\s*endproperty\s*:\s*\w+\s*;?\s*$',
        r'^\s*endsequence\s*:\s*\w+\s*;?\s*$',
        
        # property内部的时序表达式（避免漏掉）
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

def classify_assertion_type(assertion_code):
    """
    分类断言类型
    """
    clean_code = re.sub(r'//.*?$|/\*.*?\*/', '', assertion_code, flags=re.DOTALL)
    clean_code = re.sub(r'\s+', ' ', clean_code).strip()
    
    if re.search(r'^\s*property\s+\w+\s*', clean_code, re.IGNORECASE):
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
    elif re.search(r'^\s*assert\s*\(', clean_code, re.IGNORECASE):
        return "immediate_assert"
    else:
        return "unknown"

def find_assertion_files(directory):
    """
    查找指定目录及其子目录下所有包含Verilog断言语法的.sv和.v文件
    """
    file_stats = {}
    assertion_details = []
    processed_lines = set()

    base_path = Path(directory)
    sv_files = list(base_path.rglob('*.sv'))
    v_files = list(base_path.rglob('*.v'))
    verilog_files = sv_files + v_files
    
    print(f"找到 {len(verilog_files)} 个Verilog文件，开始处理...")
    
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
                    complete_assertion = extract_complete_assertion(lines, line_num)
                    if complete_assertion:
                        assertion_count += 1
                        
                        assertion_line_count = len(complete_assertion.split('\n'))
                        for i in range(line_num, line_num + assertion_line_count):
                            file_processed_lines.add(i)
                        
                        # 分类断言类型
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

def save_to_csv(file_stats, output_file):
    """将文件级别的统计结果保存到CSV文件"""
    try:
        with open(output_file, 'w', newline='', encoding='utf-8') as csvfile:
            fieldnames = ['file_name', 'file_path', 'assertion_count']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            
            writer.writeheader()
            for stats in file_stats.values():
                writer.writerow({
                    'file_name': stats['file_name'],
                    'file_path': stats['file_path'],
                    'assertion_count': stats['assertion_count']
                })
        print(f"文件统计已保存至: {output_file}")
    except IOError as e:
        print(f"错误：无法写入CSV文件 {output_file}: {str(e)}")

def save_assertion_details(assertion_details, details_file):
    """将详细的断言代码保存到CSV文件"""
    try:
        with open(details_file, 'w', newline='', encoding='utf-8') as csvfile:
            fieldnames = ['file_name', 'file_path', 'line_number', 'assertion_type', 'line_count', 'assertion_code']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            
            writer.writeheader()
            for detail in assertion_details:
                cleaned_code = re.sub(r'\s+', ' ', detail['assertion_code'].replace('\n', ' ')).strip()
                writer.writerow({
                    'file_name': detail['file_name'],
                    'file_path': detail['file_path'],
                    'line_number': detail['line_number'],
                    'assertion_type': detail['assertion_type'],
                    'line_count': detail['line_count'],
                    'assertion_code': cleaned_code[:500]  # 限制长度但保留更多内容
                })
        print(f"详细断言已保存至: {details_file}")
    except IOError as e:
        print(f"错误：无法写入详细断言文件 {details_file}: {str(e)}")

def save_type_statistics(assertion_details, stats_file):
    """保存断言类型统计"""
    type_stats = {}
    for detail in assertion_details:
        a_type = detail['assertion_type']
        type_stats[a_type] = type_stats.get(a_type, 0) + 1
    
    try:
        with open(stats_file, 'w', newline='', encoding='utf-8') as csvfile:
            fieldnames = ['assertion_type', 'count', 'percentage']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            
            writer.writeheader()
            total = len(assertion_details)
            for a_type, count in sorted(type_stats.items(), key=lambda x: x[1], reverse=True):
                percentage = (count / total * 100) if total > 0 else 0
                writer.writerow({
                    'assertion_type': a_type,
                    'count': count,
                    'percentage': f"{percentage:.2f}%"
                })
        print(f"类型统计已保存至: {stats_file}")
    except IOError as e:
        print(f"错误：无法写入类型统计文件 {stats_file}: {str(e)}")

def main():
    target_directory = "/home/zhaiqingchen/assertion_workspace/dataset/verilog-repos2/2020/1"
    output_csv = "/home/zhaiqingchen/assertion_workspace/assertion_results/test/assertion_results_test.csv"
    details_csv = "/home/zhaiqingchen/assertion_workspace/assertion_results/test/assertion_details_test.csv"
    stats_csv = "/home/zhaiqingchen/assertion_workspace/assertion_results/test/assertion_type_stats_test.csv"
    examples_dir = "/home/zhaiqingchen/assertion_workspace/assertion_results/test/assertion_examples_test"

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
    
    # 显示property相关的示例
    property_examples = [d for d in assertion_details if 'property' in d['assertion_type']]
    if property_examples:
        print(f"\nProperty声明示例 (前2个):")
        for i, example in enumerate(property_examples[:2], 1):
            print(f"{i}. {example['assertion_code'][:200]}...")

if __name__ == "__main__":
    main()
