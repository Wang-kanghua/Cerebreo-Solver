import os
import re
import csv
from pathlib import Path
from collections import Counter
import statistics

def extract_complete_assertion(lines, start_line_num):
    """
    从起始行开始提取完整的断言语句
    """
    assertion_lines = []
    brace_count = 0
    parenthesis_count = 0
    bracket_count = 0
    in_assertion = False
    found_start = False
    
    for i in range(start_line_num - 1, min(start_line_num + 10, len(lines))):  # 限制搜索范围
        line = lines[i].rstrip()  # 保留右侧空白用于格式
        line_clean = line.strip()
        
        if not in_assertion:
            # 精确匹配断言开始
            if re.match(r'^\s*(assert|assume|cover|restrict)\b', line_clean):
                in_assertion = True
                found_start = True
                assertion_lines.append(line)
                # 统计括号
                parenthesis_count += line_clean.count('(') - line_clean.count(')')
                brace_count += line_clean.count('{') - line_clean.count('}')
                bracket_count += line_clean.count('[') - line_clean.count(']')
                
                # 检查是否已经是完整的一行断言
                if (parenthesis_count == 0 and brace_count == 0 and bracket_count == 0 
                    and line_clean.endswith(';')):
                    break
                continue
        
        if in_assertion:
            assertion_lines.append(line)
            # 更新括号计数
            parenthesis_count += line_clean.count('(') - line_clean.count(')')
            brace_count += line_clean.count('{') - line_clean.count('}')
            bracket_count += line_clean.count('[') - line_clean.count(']')
            
            # 检查断言是否结束
            if (parenthesis_count == 0 and brace_count == 0 and bracket_count == 0 
                and line_clean.endswith(';')):
                break
            if any(keyword in line_clean for keyword in ['endproperty', 'endsequence']):
                break
    
    if not found_start:
        return ""
                
    return '\n'.join(assertion_lines).strip()

def is_verilog_assertion(line):
    """
    精确检测Verilog断言
    """
    line_clean = line.strip()
    
    # 跳过注释和预处理指令
    if (not line_clean or 
        line_clean.startswith(('//', '/*', '*', '`', '#'))):
        return False
    
    # 移除行内注释
    line_clean = re.sub(r'//.*$', '', line_clean)
    line_clean = re.sub(r'/\*.*?\*/', '', line_clean).strip()
    
    # 精确匹配断言模式
    patterns = [
        r'^\s*(assert|assume|cover|restrict)\s*\([^)]+\)\s*;',
        r'^\s*(assert|assume|cover|restrict)\s+property\s*\([^)]+\)\s*;',
        r'^\s*\w+\s*:\s*(assert|assume|cover|restrict)\s*\([^)]+\)\s*;',
        r'^\s*property\s+\w+\s*;',
        r'^\s*sequence\s+\w+\s*;',
    ]
    
    return any(re.search(pattern, line_clean, re.IGNORECASE) for pattern in patterns)

def analyze_assertion_type(assertion_code):
    """
    分析断言类型
    """
    code_lower = assertion_code.lower()
    
    if 'property' in code_lower:
        return 'concurrent'
    elif 'sequence' in code_lower:
        return 'sequence'
    elif 'assume' in code_lower:
        return 'assume'
    elif 'cover' in code_lower:
        return 'cover'
    elif 'restrict' in code_lower:
        return 'restrict'
    else:
        return 'immediate'

def has_assertion_label(assertion_code):
    """
    检查断言是否有标签
    """
    # 匹配格式: label: assert(...);
    return bool(re.search(r'^\s*\w+\s*:\s*(assert|assume|cover|restrict)', assertion_code))

def count_lines_of_code(file_path):
    """
    统计文件的代码行数（排除空行和注释）
    """
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            lines = f.readlines()
        
        code_lines = 0
        for line in lines:
            line_clean = line.strip()
            if line_clean and not line_clean.startswith(('//', '/*', '*')):
                # 移除行内注释
                line_clean = re.sub(r'//.*$', '', line_clean)
                line_clean = re.sub(r'/\*.*?\*/', '', line_clean).strip()
                if line_clean:
                    code_lines += 1
        
        return code_lines
    except:
        return 0

def analyze_repository_stats(directory):
    """
    分析代码仓库的统计信息
    """
    stats = {
        'repo_count': 0,
        'verilog_files': 0,
        'files_with_assertions': 0,
        'total_assertions': 0,
        'max_assertions_per_file': 0,
        'assertion_density': 0.0,
        'labeled_assertions': 0,
        'assertion_types': Counter(),
        'file_line_counts': [],
        'assertion_files': []
    }
    
    base_path = Path(directory)
    
    # 统计Repo总数（顶层文件夹数）
    stats['repo_count'] = sum(1 for item in base_path.iterdir() if item.is_dir())
    
    # 遍历所有.v和.sv文件
    verilog_files = base_path.rglob('*.[sv]')
    
    for file_path in verilog_files:
        if not file_path.is_file():
            continue
        
        stats['verilog_files'] += 1
        file_assertions = []
        
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
            
            # 统计代码行数
            loc = count_lines_of_code(file_path)
            stats['file_line_counts'].append(loc)
            
            for line_num, line in enumerate(lines, 1):
                if is_verilog_assertion(line):
                    complete_assertion = extract_complete_assertion(lines, line_num)
                    if complete_assertion:
                        file_assertions.append({
                            'line_number': line_num,
                            'code': complete_assertion,
                            'type': analyze_assertion_type(complete_assertion),
                            'labeled': has_assertion_label(complete_assertion)
                        })
            
            if file_assertions:
                stats['files_with_assertions'] += 1
                stats['total_assertions'] += len(file_assertions)
                stats['max_assertions_per_file'] = max(stats['max_assertions_per_file'], len(file_assertions))
                
                # 记录断言文件信息
                stats['assertion_files'].append({
                    'path': str(file_path),
                    'assertion_count': len(file_assertions),
                    'loc': loc
                })
                
                # 统计类型和标签
                for assertion in file_assertions:
                    stats['assertion_types'][assertion['type']] += 1
                    if assertion['labeled']:
                        stats['labeled_assertions'] += 1
                        
        except Exception as e:
            print(f"警告：无法处理文件 {file_path}: {e}")
            continue
    
    # 计算断言密度（断言数/千行代码）
    total_loc = sum(stats['file_line_counts'])
    if total_loc > 0:
        stats['assertion_density'] = (stats['total_assertions'] / total_loc) * 1000
    
    # 计算标注比例
    if stats['total_assertions'] > 0:
        stats['labeled_ratio'] = (stats['labeled_assertions'] / stats['total_assertions']) * 100
    else:
        stats['labeled_ratio'] = 0.0
    
    # 计算类型比例
    stats['type_ratios'] = {}
    for assertion_type, count in stats['assertion_types'].items():
        stats['type_ratios'][assertion_type] = (count / stats['total_assertions']) * 100
    
    return stats

def generate_report(stats, output_file="assertion_report.csv"):
    """
    生成详细的统计报告
    """
    # 控制台输出
    print("=" * 60)
    print("VERILOG ASSERTION 统计报告")
    print("=" * 60)
    print(f"Repo总数: {stats['repo_count']}")
    print(f".v/.sv文件总数: {stats['verilog_files']}")
    print(f"包含Assertion文件数目: {stats['files_with_assertions']}")
    print(f"Assertion条目数目: {stats['total_assertions']}")
    print(f"最多Assertion的文件数目: {stats['max_assertions_per_file']}")
    print(f"Assertion密度: {stats['assertion_density']:.2f} 断言/千行代码")
    print(f"断言存在标注比例: {stats['labeled_ratio']:.1f}%")
    print("\n断言类型比例:")
    for assertion_type, ratio in stats['type_ratios'].items():
        print(f"  {assertion_type}: {ratio:.1f}%")
    
    # CSV输出
    try:
        with open(output_file, 'w', newline='', encoding='utf-8') as csvfile:
            writer = csv.writer(csvfile)
            
            # 写入基本统计
            writer.writerow(["统计项", "数值"])
            writer.writerow(["Repo总数", stats['repo_count']])
            writer.writerow([".v/.sv文件总数", stats['verilog_files']])
            writer.writerow(["包含Assertion文件数目", stats['files_with_assertions']])
            writer.writerow(["Assertion条目数目", stats['total_assertions']])
            writer.writerow(["最多Assertion的文件数目", stats['max_assertions_per_file']])
            writer.writerow(["Assertion密度", f"{stats['assertion_density']:.2f}"])
            writer.writerow(["断言存在标注比例", f"{stats['labeled_ratio']:.1f}%"])
            
            writer.writerow([])
            writer.writerow(["断言类型", "数量", "比例"])
            for assertion_type, count in stats['assertion_types'].items():
                ratio = (count / stats['total_assertions']) * 100
                writer.writerow([assertion_type, count, f"{ratio:.1f}%"])
            
            # 写入包含断言的文件列表
            writer.writerow([])
            writer.writerow(["包含断言的文件列表"])
            writer.writerow(["文件路径", "断言数量", "代码行数"])
            for file_info in sorted(stats['assertion_files'], key=lambda x: x['assertion_count'], reverse=True)[:20]:
                writer.writerow([file_info['path'], file_info['assertion_count'], file_info['loc']])
                
    except Exception as e:
        print(f"无法写入CSV文件: {e}")

def main():
    target_directory = ""
    output_csv = "assertion_statistics_report.csv"
    
    if not os.path.isdir(target_directory):
        print(f"错误：目录 {target_directory} 不存在！")
        return
    
    print("正在分析代码仓库...")
    stats = analyze_repository_stats(target_directory)
    
    generate_report(stats, output_csv)
    print(f"\n详细报告已保存至: {output_csv}")

if __name__ == "__main__":
    main()
