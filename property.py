import os
import re
import csv
from pathlib import Path

def extract_complete_property(lines, start_line_num):
    """
    从起始行开始提取完整的property段落
    """
    property_lines = []
    in_property = False
    found_property_start = False
    endproperty_found = False
    
    # 从起始行开始向后查找完整的property
    for i in range(start_line_num - 1, min(start_line_num + 50, len(lines))):
        original_line = lines[i]
        line_clean = original_line.strip()
        
        if not in_property:
            # 匹配property开始
            if re.match(r'^\s*property\s+\w+\s*;', line_clean):
                in_property = True
                found_property_start = True
                property_lines.append(original_line)
                continue
        
        if in_property:
            property_lines.append(original_line)
            
            # 检查property是否结束
            if re.search(r'endproperty\s*:', line_clean) or re.search(r'endproperty\s*;', line_clean):
                endproperty_found = True
                break
    
    # 如果没有找到完整的property，返回空
    if not found_property_start or not endproperty_found:
        return ""
                
    return ''.join(property_lines).rstrip()

def is_property_definition(line):
    """
    检测是否为property定义开始
    """
    # 清理行内容
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
    
    # 检查property定义语法
    property_patterns = [
        r'^\s*property\s+\w+\s*;',
        r'^\s*property\s+\w+\s*\([^)]*\)\s*;',
    ]
    
    for pattern in property_patterns:
        if re.search(pattern, line_clean, re.IGNORECASE):
            return True
    
    return False

def find_property_files(directory):
    """
    查找指定目录及其子目录下所有包含property定义的.sv和.v文件
    返回匹配文件的路径列表和包含完整property的统计信息
    """
    file_stats = {}
    property_details = []  # 存储每个property的详细信息
    processed_lines = set()  # 记录已经处理过的行号

    # 使用Path对象进行文件遍历
    base_path = Path(directory)
    sv_files = list(base_path.rglob('*.sv'))
    v_files = list(base_path.rglob('*.v'))
    verilog_files = sv_files + v_files
    
    print(f"找到 {len(verilog_files)} 个Verilog文件，开始处理...")
    
    for file_idx, file_path in enumerate(verilog_files, 1):
        if not file_path.is_file():
            continue
        
        # 每处理100个文件输出一次进度
        if file_idx % 100 == 0:
            print(f"已处理 {file_idx}/{len(verilog_files)} 个文件...")
            
        property_count = 0
        file_properties = []  # 存储当前文件的所有property
        file_processed_lines = set()  # 当前文件已处理的行号
        
        try:
            # 读取整个文件内容以便处理多行property
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
            
            for line_num, line in enumerate(lines, 1):
                # 跳过已经处理过的行
                if line_num in file_processed_lines:
                    continue
                    
                if is_property_definition(line):
                    # 提取完整的property代码
                    complete_property = extract_complete_property(lines, line_num)
                    if complete_property:
                        property_count += 1
                        
                        # 计算这个property占用了多少行
                        property_line_count = len(complete_property.split('\n'))
                        # 标记这些行为已处理，避免重复提取
                        for i in range(line_num, line_num + property_line_count):
                            file_processed_lines.add(i)
                        
                        # 提取property名称
                        property_name = extract_property_name(complete_property)
                        
                        file_properties.append({
                            'line_number': line_num,
                            'name': property_name,
                            'code': complete_property,
                            'line_count': property_line_count
                        })
                        
                        # 添加到详细列表
                        property_details.append({
                            'file_name': file_path.name,
                            'file_path': str(file_path),
                            'line_number': line_num,
                            'property_name': property_name,
                            'property_code': complete_property,
                            'line_count': property_line_count
                        })

            if property_count > 0:
                file_stats[str(file_path)] = {
                    'file_name': file_path.name,
                    'property_count': property_count,
                    'file_path': str(file_path),
                    'properties': file_properties  # 保存该文件的所有property
                }

        except (IOError, UnicodeDecodeError, PermissionError) as e:
            print(f"警告：无法读取文件 {file_path}: {str(e)}")
            continue

    return file_stats, property_details

def extract_property_name(property_code):
    """
    从property代码中提取property名称
    """
    # 匹配 property AssertSpec6; 这样的模式
    name_pattern = r'property\s+(\w+)\s*[;\(]'
    match = re.search(name_pattern, property_code)
    if match:
        return match.group(1)
    return "Unknown"

def save_to_csv(file_stats, output_file):
    """将文件级别的统计结果保存到CSV文件"""
    try:
        with open(output_file, 'w', newline='', encoding='utf-8') as csvfile:
            fieldnames = ['file_name', 'file_path', 'property_count']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            
            writer.writeheader()
            for stats in file_stats.values():
                writer.writerow({
                    'file_name': stats['file_name'],
                    'file_path': stats['file_path'],
                    'property_count': stats['property_count']
                })
        print(f"文件统计已保存至: {output_file}")
    except IOError as e:
        print(f"错误：无法写入CSV文件 {output_file}: {str(e)}")
        return False
    return True

def save_property_details(property_details, details_file):
    """将详细的property代码保存到单独的CSV文件"""
    try:
        with open(details_file, 'w', newline='', encoding='utf-8') as csvfile:
            fieldnames = ['file_name', 'file_path', 'line_number', 'property_name', 'property_code', 'line_count']
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
            
            writer.writeheader()
            for detail in property_details:
                # 清理代码，移除多余的空格但保留基本结构
                cleaned_code = re.sub(r'\s+', ' ', detail['property_code'].replace('\n', ' ')).strip()
                writer.writerow({
                    'file_name': detail['file_name'],
                    'file_path': detail['file_path'],
                    'line_number': detail['line_number'],
                    'property_name': detail['property_name'],
                    'property_code': cleaned_code,
                    'line_count': detail['line_count']
                })
        print(f"详细property已保存至: {details_file}")
    except IOError as e:
        print(f"错误：无法写入详细property文件 {details_file}: {str(e)}")
        return False
    return True

def save_property_examples(file_stats, examples_dir):
    """为每个文件保存property代码示例到单独的文本文件"""
    if not os.path.exists(examples_dir):
        os.makedirs(examples_dir)
    
    example_count = 0
    for file_path, stats in file_stats.items():
        if stats['property_count'] > 0:
            # 创建安全的文件名
            safe_filename = re.sub(r'[^\w\.]', '_', stats['file_name'])
            example_file = os.path.join(examples_dir, f"{safe_filename}_properties.txt")
            
            try:
                with open(example_file, 'w', encoding='utf-8') as f:
                    f.write(f"File: {stats['file_name']}\n")
                    f.write(f"Path: {stats['file_path']}\n")
                    f.write(f"Total properties: {stats['property_count']}\n")
                    f.write("=" * 80 + "\n\n")
                    
                    for i, prop in enumerate(stats['properties'], 1):
                        f.write(f"Property {i}: {prop['name']} (Line {prop['line_number']}, {prop['line_count']} lines):\n")
                        f.write("-" * 60 + "\n")
                        f.write(prop['code'])
                        f.write("\n\n")
                
                example_count += 1
                        
            except IOError as e:
                print(f"警告：无法写入示例文件 {example_file}: {str(e)}")
    
    print(f"生成 {example_count} 个示例文件在目录: {examples_dir}")

def main():
    target_directory = ""
    output_csv = "property_results_2024.csv"
    details_csv = "property_details_2024.csv"
    examples_dir = "property_examples_2024"

    if not os.path.isdir(target_directory):
        print(f"错误：目录 {target_directory} 不存在！")
        return

    print(f"正在搜索目录: {target_directory}...")
    file_stats, property_details = find_property_files(target_directory)

    # 保存各种格式的结果
    save_to_csv(file_stats, output_csv)
    save_property_details(property_details, details_csv)
    save_property_examples(file_stats, examples_dir)
    
    # 输出统计信息
    total_files = len(file_stats)
    total_properties = sum(stats['property_count'] for stats in file_stats.values())
    
    print(f"\n处理完成！")
    print(f"结果文件:")
    print(f"  - 文件统计: {output_csv}")
    print(f"  - 详细property: {details_csv}")
    print(f"  - 代码示例: {examples_dir}/")
    print(f"\n总计: {total_files} 个.sv/.v文件包含property定义")
    print(f"总property数量: {total_properties}")
    
    # 输出前5个包含最多property的文件
    if file_stats:
        print("\n包含property最多的文件:")
        sorted_files = sorted(file_stats.items(), 
                            key=lambda x: x[1]['property_count'], 
                            reverse=True)[:5]
        for file_path, stats in sorted_files:
            print(f"  {stats['file_name']}: {stats['property_count']} 个property")
    
    # 显示一些property示例
    if property_details:
        print(f"\nProperty示例 (前3个):")
        for i, detail in enumerate(property_details[:3], 1):
            print(f"{i}. {detail['property_name']}:")
            print(f"   {detail['property_code'][:100]}...")
            print()

if __name__ == "__main__":
    main()
