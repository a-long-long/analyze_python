import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog
import ast
import traceback
import sys
import os
import struct
import marshal
import py_compile
import importlib.util
from collections import defaultdict
import dis
import types
import inspect

class AdvancedCodeAnalyzer(ast.NodeVisitor):
    def __init__(self):
        self.functions = {}
        self.classes = {}
        self.variables = defaultdict(list)
        self.flow = []
        self.current_scope = None
        self.errors = []
        self.imports = []
        self.function_calls = defaultdict(list)
        self.class_inheritance = {}
        self.class_methods = defaultdict(list)
        self.method_calls = defaultdict(list)
        self.variable_dependencies = defaultdict(set)
        self.control_flow = []
        self.data_flow = []
        self.bytecode_info = []
        
    def visit_Import(self, node):
        try:
            for alias in node.names:
                self.imports.append({
                    'type': 'import',
                    'name': alias.name,
                    'alias': alias.asname,
                    'line': getattr(node, 'lineno', 0)
                })
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理Import时出错: {str(e)}")
            
    def visit_ImportFrom(self, node):
        try:
            module = node.module or ''
            for alias in node.names:
                self.imports.append({
                    'type': 'from',
                    'module': module,
                    'name': alias.name,
                    'alias': alias.asname,
                    'line': getattr(node, 'lineno', 0)
                })
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理ImportFrom时出错: {str(e)}")

    def visit_FunctionDef(self, node):
        try:
            lineno = getattr(node, 'lineno', 0)
            args_list = []
            try:
                if hasattr(node, 'args') and hasattr(node.args, 'args'):
                    args_list = [getattr(arg, 'arg', '') for arg in node.args.args]
            except:
                pass
                
            func_info = {
                'lineno': lineno,
                'args': args_list,
                'scope': self.current_scope,
                'calls': [],
                'called_by': [],
                'variables': [],
                'returns': []
            }
            
            func_name = getattr(node, 'name', 'unknown')
            self.functions[func_name] = func_info
            old_scope = self.current_scope
            self.current_scope = func_name
            
            if old_scope and old_scope in self.classes:
                self.class_methods[old_scope].append(func_name)
                
            self.generic_visit(node)
            self.current_scope = old_scope
            
        except Exception as e:
            self.errors.append(f"处理函数时出错: {str(e)}")

    def visit_ClassDef(self, node):
        try:
            lineno = getattr(node, 'lineno', 0)
            
            bases = []
            try:
                for base in node.bases:
                    if isinstance(base, ast.Name):
                        bases.append(base.id)
                    elif isinstance(base, ast.Attribute):
                        bases.append(str(base))
            except:
                pass
            
            self.classes[getattr(node, 'name', 'unknown')] = {
                'lineno': lineno,
                'bases': bases,
                'methods': [],
                'attributes': []
            }
            
            old_scope = self.current_scope
            self.current_scope = getattr(node, 'name', 'unknown')
            self.generic_visit(node)
            self.current_scope = old_scope
            
        except Exception as e:
            self.errors.append(f"处理类时出错: {str(e)}")

    def visit_Assign(self, node):
        try:
            lineno = getattr(node, 'lineno', 0)
            for target in getattr(node, 'targets', []):
                if hasattr(target, 'id'):
                    var_name = getattr(target, 'id', 'unknown')
                    self.variables[var_name].append(('赋值', lineno, self.current_scope))
                    if self.current_scope:
                        if self.current_scope in self.functions:
                            if var_name not in self.functions[self.current_scope]['variables']:
                                self.functions[self.current_scope]['variables'].append(var_name)
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理赋值语句时出错: {str(e)}")

    def visit_Name(self, node):
        try:
            var_name = getattr(node, 'id', 'unknown')
            lineno = getattr(node, 'lineno', 0)
            
            if isinstance(getattr(node, 'ctx', None), ast.Load):
                self.variables[var_name].append(('使用', lineno, self.current_scope))
                if self.current_scope:
                    self.variable_dependencies[var_name].add(self.current_scope)
            elif isinstance(getattr(node, 'ctx', None), ast.Store):
                self.variables[var_name].append(('赋值', lineno, self.current_scope))
                
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理名称时出错: {str(e)}")
            
    def visit_Call(self, node):
        try:
            lineno = getattr(node, 'lineno', 0)
            func_name = 'unknown'
            
            if isinstance(getattr(node, 'func', None), ast.Name):
                func_name = getattr(node.func, 'id', 'unknown')
            elif isinstance(getattr(node, 'func', None), ast.Attribute):
                if isinstance(node.func.value, ast.Name):
                    obj_name = node.func.value.id
                    method_name = node.func.attr
                    func_name = f"{obj_name}.{method_name}"
                    self.method_calls[obj_name].append({
                        'method': method_name,
                        'line': lineno,
                        'caller': self.current_scope
                    })
            
            if self.current_scope:
                if self.current_scope in self.functions:
                    self.functions[self.current_scope]['calls'].append({
                        'function': func_name,
                        'line': lineno
                    })
                if func_name in self.functions:
                    self.functions[func_name]['called_by'].append({
                        'function': self.current_scope,
                        'line': lineno
                    })
                    
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理函数调用时出错: {str(e)}")
            
    def visit_Return(self, node):
        try:
            lineno = getattr(node, 'lineno', 0)
            if self.current_scope and self.current_scope in self.functions:
                self.functions[self.current_scope]['returns'].append({
                    'line': lineno,
                    'value': getattr(node, 'value', None)
                })
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理返回语句时出错: {str(e)}")
            
    def visit_If(self, node):
        try:
            lineno = getattr(node, 'lineno', 0)
            self.control_flow.append({
                'type': 'if',
                'line': lineno,
                'scope': self.current_scope
            })
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理if语句时出错: {str(e)}")
            
    def visit_For(self, node):
        try:
            lineno = getattr(node, 'lineno', 0)
            self.control_flow.append({
                'type': 'for',
                'line': lineno,
                'scope': self.current_scope
            })
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理for循环时出错: {str(e)}")
            
    def visit_While(self, node):
        try:
            lineno = getattr(node, 'lineno', 0)
            self.control_flow.append({
                'type': 'while',
                'line': lineno,
                'scope': self.current_scope
            })
            self.generic_visit(node)
        except Exception as e:
            self.errors.append(f"处理while循环时出错: {str(e)}")

class BinaryAnalyzer:
    """二进制文件分析器"""
    def __init__(self):
        self.errors = []
        self.metadata = {}
        self.bytecode_info = []
        self.imports = []
        self.functions = {}
        self.classes = {}
        
    def analyze_pyc(self, file_path):
        """分析 .pyc 文件"""
        try:
            with open(file_path, 'rb') as f:
                # 读取 .pyc 文件头
                magic = f.read(4)
                bit_field = f.read(4)
                timestamp = f.read(4)
                size = f.read(4)
                
                self.metadata['magic'] = magic.hex()
                self.metadata['bit_field'] = bit_field.hex()
                self.metadata['timestamp'] = int.from_bytes(timestamp, 'little')
                self.metadata['size'] = int.from_bytes(size, 'little')
                
                # 读取编组的代码对象
                try:
                    code_obj = marshal.load(f)
                    if isinstance(code_obj, types.CodeType):
                        self._analyze_code_object(code_obj)
                except Exception as e:
                    self.errors.append(f"反编组代码对象失败: {str(e)}")
                    
        except Exception as e:
            self.errors.append(f"读取 .pyc 文件失败: {str(e)}")
            
    def analyze_py(self, file_path):
        """分析 .py 文件并生成字节码信息"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                source_code = f.read()
                
            # 编译源码为代码对象
            code_obj = compile(source_code, file_path, 'exec')
            self._analyze_code_object(code_obj)
            
        except Exception as e:
            self.errors.append(f"分析 .py 文件失败: {str(e)}")
            
    def _analyze_code_object(self, code_obj):
        """分析代码对象"""
        try:
            # 获取基本信息
            self.metadata['filename'] = getattr(code_obj, 'co_filename', 'unknown')
            self.metadata['name'] = getattr(code_obj, 'co_name', 'unknown')
            self.metadata['argcount'] = getattr(code_obj, 'co_argcount', 0)
            self.metadata['varnames'] = list(getattr(code_obj, 'co_varnames', []))
            self.metadata['names'] = list(getattr(code_obj, 'co_names', []))
            self.metadata['consts'] = list(getattr(code_obj, 'co_consts', []))
            self.metadata['flags'] = getattr(code_obj, 'co_flags', 0)
            
            # 反汇编字节码
            instructions = list(dis.get_instructions(code_obj))
            for instr in instructions:
                self.bytecode_info.append({
                    'offset': instr.offset,
                    'opname': instr.opname,
                    'arg': instr.arg,
                    'argval': instr.argval,
                    'argrepr': instr.argrepr,
                    'lineno': instr.starts_line
                })
                
            # 分析导入
            for name in self.metadata['names']:
                if name in ['import', 'from']:
                    self.imports.append({'name': name, 'type': 'unknown'})
                    
            # 分析函数和类（简单提取）
            if isinstance(self.metadata['consts'], list):
                for const in self.metadata['consts']:
                    if isinstance(const, types.CodeType):
                        func_name = getattr(const, 'co_name', 'unknown')
                        self.functions[func_name] = {
                            'lineno': getattr(const, 'co_firstlineno', 0),
                            'argcount': getattr(const, 'co_argcount', 0),
                            'varnames': list(getattr(const, 'co_varnames', []))
                        }
                        
        except Exception as e:
            self.errors.append(f"分析代码对象失败: {str(e)}")
            
    def analyze_executable(self, file_path):
        """分析可执行文件的基本信息"""
        try:
            file_size = os.path.getsize(file_path)
            self.metadata['file_size'] = file_size
            
            with open(file_path, 'rb') as f:
                # 读取文件头以识别文件类型
                header = f.read(1024)
                
                # 检查是否为 Python 可执行文件
                if b'Python' in header:
                    self.metadata['type'] = 'Python Executable'
                elif header.startswith(b'\x7fELF'):
                    self.metadata['type'] = 'ELF Executable'
                elif header.startswith(b'MZ'):
                    self.metadata['type'] = 'Windows Executable'
                else:
                    self.metadata['type'] = 'Unknown Executable'
                    
                # 读取前几KB进行格式分析
                self.metadata['header_hex'] = header[:64].hex()
                
        except Exception as e:
            self.errors.append(f"分析可执行文件失败: {str(e)}")

class CodeAnalyzerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title('高级Python代码分析器 - 支持二进制文件分析')
        self.root.geometry("1300x850")
        
        self.analyzer = None
        self.binary_analyzer = None
        self.current_file_type = None
        self.setup_ui()
        
    def setup_ui(self):
        try:
            # 主框架
            main_frame = ttk.Frame(self.root, padding="5")
            main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
            self.root.columnconfigure(0, weight=1)
            self.root.rowconfigure(0, weight=1)
            
            # 工具栏
            toolbar_frame = ttk.Frame(main_frame)
            toolbar_frame.grid(row=0, column=0, columnspan=2, sticky=(tk.W, tk.E), pady=(0, 5))
            
            self.open_btn = ttk.Button(toolbar_frame, text='打开文件', command=self.open_file)
            self.open_btn.pack(side=tk.LEFT, padx=(0, 5))
            
            self.analyze_btn = ttk.Button(toolbar_frame, text='分析', command=self.analyze_code)
            self.analyze_btn.pack(side=tk.LEFT, padx=(0, 5))
            
            ttk.Label(toolbar_frame, text="分析类型:").pack(side=tk.LEFT, padx=(20, 5))
            self.analysis_type = tk.StringVar(value="source")
            type_combo = ttk.Combobox(toolbar_frame, textvariable=self.analysis_type, 
                                     values=["source", "binary", "executable"], 
                                     state="readonly", width=12)
            type_combo.pack(side=tk.LEFT, padx=(0, 5))
            
            ttk.Label(toolbar_frame, text="分析级别:").pack(side=tk.LEFT, padx=(20, 5))
            self.detail_level = tk.StringVar(value="basic")
            detail_combo = ttk.Combobox(toolbar_frame, textvariable=self.detail_level, 
                                       values=["basic", "advanced", "complete", "binary"], 
                                       state="readonly", width=12)
            detail_combo.pack(side=tk.LEFT, padx=(0, 5))
            
            # 代码区域
            code_frame = ttk.LabelFrame(main_frame, text="代码/字节码", padding="5")
            code_frame.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S), padx=(0, 5))
            main_frame.columnconfigure(0, weight=1)
            main_frame.rowconfigure(1, weight=1)
            
            self.code_text = scrolledtext.ScrolledText(code_frame, wrap=tk.NONE, font=('Consolas', 10))
            self.code_text.pack(fill=tk.BOTH, expand=True)
            self.code_text.insert('1.0', """def fibonacci(n):
    if n <= 1:
        return n
    else:
        return fibonacci(n-1) + fibonacci(n-2)

def calculate_fibonacci_sequence(count):
    sequence = []
    for i in range(count):
        sequence.append(fibonacci(i))
    return sequence

class MathCalculator:
    def __init__(self):
        self.history = []
    
    def add(self, a, b):
        result = a + b
        self.history.append(f"{a} + {b} = {result}")
        return result
    
    def multiply(self, a, b):
        result = a * b
        self.history.append(f"{a} * {b} = {result}")
        return result
    
    def get_history(self):
        return self.history

def main():
    calc = MathCalculator()
    x = 10
    y = 20
    sum_result = calc.add(x, y)
    mul_result = calc.multiply(x, y)
    fib_sequence = calculate_fibonacci_sequence(10)
    print(f"Sum: {sum_result}")
    print(f"Product: {mul_result}")
    print(f"Fibonacci: {fib_sequence}")

if __name__ == "__main__":
    main()""")
            
            # 结果区域 - 使用Notebook
            notebook_frame = ttk.Frame(main_frame)
            notebook_frame.grid(row=1, column=1, sticky=(tk.W, tk.E, tk.N, tk.S))
            main_frame.columnconfigure(1, weight=1)
            
            self.notebook = ttk.Notebook(notebook_frame)
            self.notebook.pack(fill=tk.BOTH, expand=True)
            
            # 基础分析结果
            self.basic_frame = ttk.Frame(self.notebook)
            self.notebook.add(self.basic_frame, text='基础分析')
            
            self.basic_text = scrolledtext.ScrolledText(self.basic_frame, wrap=tk.WORD, font=('Arial', 10))
            self.basic_text.pack(fill=tk.BOTH, expand=True)
            self.basic_text.insert(tk.END, '请先分析代码...')
            
            # 高级分析结果
            self.advanced_frame = ttk.Frame(self.notebook)
            self.notebook.add(self.advanced_frame, text='关系分析')
            
            self.advanced_text = scrolledtext.ScrolledText(self.advanced_frame, wrap=tk.WORD, font=('Arial', 10))
            self.advanced_text.pack(fill=tk.BOTH, expand=True)
            
            # 完整分析结果
            self.complete_frame = ttk.Frame(self.notebook)
            self.notebook.add(self.complete_frame, text='完整分析')
            
            self.complete_text = scrolledtext.ScrolledText(self.complete_frame, wrap=tk.WORD, font=('Arial', 10))
            self.complete_text.pack(fill=tk.BOTH, expand=True)
            
            # 二进制分析结果
            self.binary_frame = ttk.Frame(self.notebook)
            self.notebook.add(self.binary_frame, text='二进制分析')
            
            self.binary_text = scrolledtext.ScrolledText(self.binary_frame, wrap=tk.WORD, font=('Consolas', 9))
            self.binary_text.pack(fill=tk.BOTH, expand=True)
            
            # 错误信息
            self.error_frame = ttk.Frame(self.notebook)
            self.notebook.add(self.error_frame, text='错误信息')
            
            self.error_text = scrolledtext.ScrolledText(self.error_frame, wrap=tk.WORD, font=('Arial', 10))
            self.error_text.pack(fill=tk.BOTH, expand=True)
            
            # 状态栏
            self.status_var = tk.StringVar(value='就绪')
            self.status_bar = ttk.Label(main_frame, textvariable=self.status_var, relief=tk.SUNKEN)
            self.status_bar.grid(row=2, column=0, columnspan=2, sticky=(tk.W, tk.E), pady=(5, 0))
            
        except Exception as e:
            print(f"UI初始化错误: {e}")
            
    def open_file(self):
        try:
            file_path = filedialog.askopenfilename(
                title="打开文件",
                filetypes=[
                    ("Python files", "*.py *.pyc"),
                    ("Executable files", "*.exe *.bin"),
                    ("All files", "*.*")
                ]
            )
            if file_path:
                self.current_file_path = file_path
                file_ext = os.path.splitext(file_path)[1].lower()
                
                # 根据文件扩展名判断文件类型
                if file_ext == '.pyc':
                    self.analysis_type.set('binary')
                    self.current_file_type = 'pyc'
                elif file_ext == '.py':
                    self.analysis_type.set('source')
                    self.current_file_type = 'py'
                elif file_ext in ['.exe', '.bin']:
                    self.analysis_type.set('executable')
                    self.current_file_type = 'exe'
                else:
                    self.current_file_type = 'unknown'
                
                try:
                    # 尝试以文本方式读取源码文件
                    if file_ext == '.py':
                        with open(file_path, 'r', encoding='utf-8') as file:
                            content = file.read()
                            self.code_text.delete('1.0', tk.END)
                            self.code_text.insert('1.0', content)
                    else:
                        # 对于二进制文件，显示十六进制内容
                        with open(file_path, 'rb') as file:
                            content = file.read(1024)  # 只读取前1KB
                            hex_content = ' '.join(f'{b:02x}' for b in content)
                            self.code_text.delete('1.0', tk.END)
                            self.code_text.insert('1.0', f"Binary file (first 1KB hex):\n{hex_content}")
                            
                    self.status_var.set(f"已打开: {file_path}")
                except UnicodeDecodeError:
                    try:
                        with open(file_path, 'r', encoding='gbk') as file:
                            content = file.read()
                            self.code_text.delete('1.0', tk.END)
                            self.code_text.insert('1.0', content)
                        self.status_var.set(f"已打开: {file_path}")
                    except Exception as e2:
                        messagebox.showerror("错误", f"无法读取文件: {str(e2)}")
        except Exception as e:
            messagebox.showerror("错误", f"打开文件失败: {str(e)}")
    
    def goto_line(self, line_number):
        """跳转到指定行"""
        try:
            if line_number and line_number > 0:
                # 跳转到指定行
                self.code_text.see(f"{line_number}.0")
                self.code_text.mark_set(tk.INSERT, f"{line_number}.0")
                self.code_text.focus_set()
                
                # 修复：先清除所有旧的高亮
                self.code_text.tag_remove("highlight", "1.0", tk.END)
                # 高亮显示该行
                self.code_text.tag_add("highlight", f"{line_number}.0", f"{line_number}.end")
                self.code_text.tag_config("highlight", background="yellow", foreground="black")
                
                # 滚动到行中间位置
                self.code_text.see(f"{line_number}.0")
                
                self.status_var.set(f"跳转到第 {line_number} 行")
        except Exception as e:
            self.status_var.set(f"跳转错误: {str(e)}")
                
    def analyze_code(self):
        try:
            self.status_var.set('正在分析文件...')
            self.root.update()
            
            if not hasattr(self, 'current_file_path'):
                messagebox.showerror("错误", "请先打开文件")
                self.status_var.set('就绪')
                return
                
            file_path = self.current_file_path
            analysis_type = self.analysis_type.get()
            
            # 清空之前的分析结果
            self.analyzer = None
            self.binary_analyzer = None
            
            try:
                if analysis_type == 'source' and self.current_file_type in ['py', 'unknown']:
                    # 源码分析
                    self._analyze_source_code(file_path)
                elif analysis_type == 'binary' or self.current_file_type == 'pyc':
                    # 二进制文件分析
                    self._analyze_binary_file(file_path)
                elif analysis_type == 'executable' or self.current_file_type == 'exe':
                    # 可执行文件分析
                    self._analyze_executable_file(file_path)
                else:
                    messagebox.showerror("错误", f"不支持的分析类型: {analysis_type}")
                    self.status_var.set('分析失败')
                    return
                    
                # 显示结果
                self.display_basic_results()
                self.display_advanced_results()
                self.display_complete_results()
                self.display_binary_results()
                self.display_errors()
                
                self.status_var.set('分析完成')
                
            except SyntaxError as e:
                error_msg = f"语法错误在第 {e.lineno} 行: {e.msg}\n"
                self.basic_text.delete('1.0', tk.END)
                self.basic_text.insert(tk.END, error_msg)
                self.status_var.set('语法错误')
            except Exception as e:
                error_msg = f"分析错误: {str(e)}\n{traceback.format_exc()}"
                self.basic_text.delete('1.0', tk.END)
                self.basic_text.insert(tk.END, error_msg)
                self.status_var.set('分析失败')
                
        except Exception as e:
            error_msg = f"分析处理错误: {str(e)}\n{traceback.format_exc()}"
            self.basic_text.delete('1.0', tk.END)
            self.basic_text.insert(tk.END, error_msg)
            self.status_var.set('分析处理失败')
            
    def _analyze_source_code(self, file_path):
        """分析源代码文件"""
        with open(file_path, 'r', encoding='utf-8') as f:
            code = f.read()
            tree = ast.parse(code)
            self.analyzer = AdvancedCodeAnalyzer()
            self.analyzer.visit(tree)
            
    def _analyze_binary_file(self, file_path):
        """分析二进制文件"""
        self.binary_analyzer = BinaryAnalyzer()
        file_ext = os.path.splitext(file_path)[1].lower()
        
        if file_ext == '.pyc':
            self.binary_analyzer.analyze_pyc(file_path)
        elif file_ext == '.py':
            self.binary_analyzer.analyze_py(file_path)
        else:
            self.binary_analyzer.errors.append(f"不支持的二进制文件类型: {file_ext}")
            
    def _analyze_executable_file(self, file_path):
        """分析可执行文件"""
        self.binary_analyzer = BinaryAnalyzer()
        self.binary_analyzer.analyze_executable(file_path)
            
    def display_basic_results(self):
        try:
            # 清空之前的内容
            self.basic_text.delete('1.0', tk.END)
            
            if self.analyzer:
                self._display_source_basic_results()
            elif self.binary_analyzer:
                self._display_binary_basic_results()
            else:
                self.basic_text.insert(tk.END, '请先分析文件...')
                
        except Exception as e:
            error_msg = f"显示基础结果错误: {str(e)}\n"
            self.basic_text.delete('1.0', tk.END)
            self.basic_text.insert(tk.END, error_msg)

    def _display_source_basic_results(self):
        """显示源码分析的基础结果"""
        result = ""
        
        # 显示导入信息
        if self.analyzer.imports:
            result += "=== 导入信息 ===\n"
            for imp in self.analyzer.imports:
                if imp['type'] == 'import':
                    alias_info = f" as {imp['alias']}" if imp['alias'] else ""
                    line_info = f" (行 {imp['line']})" if imp['line'] else ""
                    result += f"import {imp['name']}{alias_info}{line_info}\n"
                else:
                    alias_info = f" as {imp['alias']}" if imp['alias'] else ""
                    line_info = f" (行 {imp['line']})" if imp['line'] else ""
                    result += f"from {imp['module']} import {imp['name']}{alias_info}{line_info}\n"
            result += "\n"
        
        # 显示函数信息
        if self.analyzer.functions:
            result += "=== 函数 ===\n"
            for name, info in self.analyzer.functions.items():
                line_info = f" (行 {info['lineno']})" if info['lineno'] else ""
                result += f"函数: {name}{line_info}"
                
                if info['lineno']:
                    line_num = info['lineno']
                    result += f" [跳转到行 {line_num}]"
                
                result += "\n"
                
                if info['args']:
                    result += f"  参数: {', '.join(info['args'])}\n"
                if info['scope']:
                    result += f"  所在作用域: {info['scope']}\n"
                result += "\n"
        
        # 显示类信息
        if self.analyzer.classes:
            result += "=== 类 ===\n"
            for name, info in self.analyzer.classes.items():
                line_info = f" (行 {info['lineno']})" if info['lineno'] else ""
                result += f"类: {name}{line_info}"
                
                if info['lineno']:
                    line_num = info['lineno']
                    result += f" [跳转到行 {line_num}]"
                
                result += "\n"
                
                if info['bases']:
                    result += f"  继承: {', '.join(info['bases'])}\n"
                result += "\n"
        
        # 显示变量信息
        if self.analyzer.variables:
            result += "=== 变量 ===\n"
            for var_name, usages in list(self.analyzer.variables.items())[:20]:
                result += f"变量: {var_name}\n"
                for usage in usages[:5]:
                    usage_type, line_num, scope = usage
                    scope_info = f" 在 {scope}" if scope else ""
                    line_info = f" 行 {line_num}" if line_num else ""
                    result += f"  {usage_type}{line_info}{scope_info}"
                    
                    if line_num:
                        result += f" [跳转]"
                    
                    result += "\n"
                if len(usages) > 5:
                    result += f"  ... 还有 {len(usages) - 5} 个使用记录\n"
                result += "\n"
        
        if not result:
            result = "未发现可分析的内容"
            
        self.basic_text.insert(tk.END, result)
        self.add_jump_links(self.basic_text)

    def _display_binary_basic_results(self):
        """显示二进制文件分析的基础结果"""
        result = ""
        
        # 显示元数据
        if self.binary_analyzer.metadata:
            result += "=== 文件元数据 ===\n"
            for key, value in self.binary_analyzer.metadata.items():
                result += f"{key}: {value}\n"
            result += "\n"
            
        # 显示函数信息
        if self.binary_analyzer.functions:
            result += "=== 函数信息 (从字节码提取) ===\n"
            for name, info in self.binary_analyzer.functions.items():
                result += f"函数: {name} (行 {info['lineno']})\n"
                result += f"  参数数量: {info['argcount']}\n"
                if info['varnames']:
                    result += f"  局部变量: {', '.join(info['varnames'][:10])}\n"
                    if len(info['varnames']) > 10:
                        result += f"  ... 还有 {len(info['varnames']) - 10} 个\n"
                result += "\n"
        
        if not result:
            result = "无基础分析结果"
            
        self.basic_text.insert(tk.END, result)

    def display_advanced_results(self):
        try:
            self.advanced_text.delete('1.0', tk.END)
            
            if self.analyzer:
                self._display_source_advanced_results()
            elif self.binary_analyzer:
                self._display_binary_advanced_results()
            else:
                self.advanced_text.insert(tk.END, '请先分析文件...')
                
        except Exception as e:
            error_msg = f"显示高级结果错误: {str(e)}\n"
            self.advanced_text.delete('1.0', tk.END)
            self.advanced_text.insert(tk.END, error_msg)

    def _display_source_advanced_results(self):
        """显示源码分析的高级结果"""
        result = ""
        
        # 显示函数调用关系
        result += "=== 函数调用关系 ===\n"
        has_calls = False
        for func_name, func_info in self.analyzer.functions.items():
            if func_info['calls']:
                has_calls = True
                result += f"{func_name} 调用:\n"
                for call in func_info['calls'][:10]:
                    line_info = f" (行 {call['line']})" if call['line'] else ""
                    result += f"  -> {call['function']}{line_info}"
                    
                    if call['line']:
                        result += f" [跳转]"
                    
                    result += "\n"
                if len(func_info['calls']) > 10:
                    result += f"  ... 还有 {len(func_info['calls']) - 10} 个调用\n"
                result += "\n"
        
        if not has_calls:
            result += "未发现函数调用关系\n\n"
        
        # 显示函数被调用关系
        result += "=== 函数被调用关系 ===\n"
        has_called_by = False
        for func_name, func_info in self.analyzer.functions.items():
            if func_info['called_by']:
                has_called_by = True
                result += f"{func_name} 被调用:\n"
                for caller in func_info['called_by'][:10]:
                    line_info = f" (行 {caller['line']})" if caller['line'] else ""
                    result += f"  <- {caller['function']}{line_info}"
                    
                    if caller['line']:
                        result += f" [跳转]"
                    
                    result += "\n"
                if len(func_info['called_by']) > 10:
                    result += f"  ... 还有 {len(func_info['called_by']) - 10} 个调用者\n"
                result += "\n"
        
        if not has_called_by:
            result += "未发现函数被调用关系\n\n"
        
        # 显示类继承关系
        if self.analyzer.classes:
            result += "=== 类继承关系 ===\n"
            has_inheritance = False
            for class_name, class_info in self.analyzer.classes.items():
                if class_info['bases']:
                    has_inheritance = True
                    line_info = f" (行 {class_info['lineno']})" if class_info['lineno'] else ""
                    result += f"{class_name}{line_info}"
                    
                    if class_info['lineno']:
                        result += f" [跳转到行 {class_info['lineno']}]"
                    
                    result += f" 继承自: {', '.join(class_info['bases'])}\n"
            if not has_inheritance:
                result += "未发现类继承关系\n"
            result += "\n"
        
        # 显示类方法
        if self.analyzer.class_methods:
            result += "=== 类方法 ===\n"
            for class_name, methods in self.analyzer.class_methods.items():
                result += f"{class_name} 的方法: {', '.join(methods)}\n"
            result += "\n"
        
        # 显示控制流信息
        if self.analyzer.control_flow:
            result += "=== 控制流结构 ===\n"
            for flow in self.analyzer.control_flow[:20]:
                scope_info = f" 在 {flow['scope']}" if flow['scope'] else ""
                line_info = f" (行 {flow['line']})" if flow['line'] else ""
                result += f"{flow['type']} 语句{line_info}{scope_info}"
                
                if flow['line']:
                    result += f" [跳转]"
                
                result += "\n"
            if len(self.analyzer.control_flow) > 20:
                result += f"... 还有 {len(self.analyzer.control_flow) - 20} 个控制流结构\n"
            result += "\n"
        
        self.advanced_text.insert(tk.END, result)
        self.add_jump_links(self.advanced_text)

    def _display_binary_advanced_results(self):
        """显示二进制分析的高级结果"""
        result = ""
        
        # 显示导入信息
        if self.binary_analyzer.imports:
            result += "=== 检测到的导入 ===\n"
            for imp in self.binary_analyzer.imports[:20]:
                result += f"{imp['type']}: {imp['name']}\n"
            if len(self.binary_analyzer.imports) > 20:
                result += f"... 还有 {len(self.binary_analyzer.imports) - 20} 个\n"
            result += "\n"
        
        if not result:
            result = "无高级分析结果"
            
        self.advanced_text.insert(tk.END, result)

    def display_complete_results(self):
        try:
            self.complete_text.delete('1.0', tk.END)
            
            if self.analyzer:
                self._display_source_complete_results()
            elif self.binary_analyzer:
                self._display_binary_complete_results()
            else:
                self.complete_text.insert(tk.END, '请先分析文件...')
                
        except Exception as e:
            error_msg = f"显示完整结果错误: {str(e)}\n"
            self.complete_text.delete('1.0', tk.END)
            self.complete_text.insert(tk.END, error_msg)

    def _display_source_complete_results(self):
        """显示源码分析的完整结果"""
        result = ""
        
        # 显示函数详细信息
        if self.analyzer.functions:
            result += "=== 函数详细信息 ===\n"
            for name, info in self.analyzer.functions.items():
                result += f"函数: {name}"
                
                if info['lineno']:
                    result += f" [跳转到行 {info['lineno']}]"
                
                result += "\n"
                result += f"  定义行: {info['lineno']}\n"
                result += f"  参数: {', '.join(info['args']) if info['args'] else '无'}\n"
                result += f"  作用域: {info['scope'] or '全局'}\n"
                
                if info['variables']:
                    result += f"  使用变量: {', '.join(info['variables'])}\n"
                
                if info['returns']:
                    result += f"  返回语句: {len(info['returns'])} 个\n"
                
                if info['calls']:
                    result += f"  调用函数: {len(info['calls'])} 个\n"
                    for call in info['calls'][:5]:
                        line_info = f" (行 {call['line']})" if call['line'] else ""
                        result += f"    -> {call['function']}{line_info}"
                        
                        if call['line']:
                            result += f" [跳转]"
                        
                        result += "\n"
                    if len(info['calls']) > 5:
                        result += f"    ... 还有 {len(info['calls']) - 5} 个\n"
                
                if info['called_by']:
                    result += f"  被调用: {len(info['called_by'])} 次\n"
                    for caller in info['called_by'][:5]:
                        line_info = f" (行 {caller['line']})" if caller['line'] else ""
                        result += f"    <- {caller['function']}{line_info}"
                        
                        if caller['line']:
                            result += f" [跳转]"
                        
                        result += "\n"
                    if len(info['called_by']) > 5:
                        result += f"    ... 还有 {len(info['called_by']) - 5} 个\n"
                
                result += "\n"
        
        # 显示类详细信息
        if self.analyzer.classes:
            result += "=== 类详细信息 ===\n"
            for name, info in self.analyzer.classes.items():
                result += f"类: {name}"
                
                if info['lineno']:
                    result += f" [跳转到行 {info['lineno']}]"
                
                result += "\n"
                result += f"  定义行: {info['lineno']}\n"
                if info['bases']:
                    result += f"  父类: {', '.join(info['bases'])}\n"
                
                if name in self.analyzer.class_methods and self.analyzer.class_methods[name]:
                    result += f"  方法: {', '.join(self.analyzer.class_methods[name])}\n"
                
                result += "\n"
        
        # 显示变量依赖关系
        if self.analyzer.variable_dependencies:
            result += "=== 变量依赖关系 ===\n"
            for var_name, dependents in list(self.analyzer.variable_dependencies.items())[:30]:
                if dependents:
                    result += f"{var_name} 被以下函数使用: {', '.join(list(dependents)[:10])}\n"
                    if len(dependents) > 10:
                        result += f"  ... 还有 {len(dependents) - 10} 个\n"
            result += "\n"
        
        # 显示方法调用
        if self.analyzer.method_calls:
            result += "=== 方法调用 ===\n"
            for obj_name, calls in self.analyzer.method_calls.items():
                result += f"对象 {obj_name} 的方法调用:\n"
                for call in calls[:10]:
                    caller_info = f" 由 {call['caller']}" if call['caller'] else ""
                    line_info = f" (行 {call['line']})" if call['line'] else ""
                    result += f"  {call['method']}{line_info}{caller_info}"
                    
                    if call['line']:
                        result += f" [跳转]"
                    
                    result += "\n"
                if len(calls) > 10:
                    result += f"  ... 还有 {len(calls) - 10} 个调用\n"
            result += "\n"
        
        self.complete_text.insert(tk.END, result)
        self.add_jump_links(self.complete_text)

    def _display_binary_complete_results(self):
        """显示二进制分析的完整结果"""
        result = ""
        
        # 显示变量和常量
        if 'varnames' in self.binary_analyzer.metadata:
            result += "=== 局部变量名 ===\n"
            for var in self.binary_analyzer.metadata['varnames'][:30]:
                result += f"{var}\n"
            if len(self.binary_analyzer.metadata['varnames']) > 30:
                result += f"... 还有 {len(self.binary_analyzer.metadata['varnames']) - 30} 个\n"
            result += "\n"
            
        if 'names' in self.binary_analyzer.metadata:
            result += "=== 全局名称 ===\n"
            for name in self.binary_analyzer.metadata['names'][:30]:
                result += f"{name}\n"
            if len(self.binary_analyzer.metadata['names']) > 30:
                result += f"... 还有 {len(self.binary_analyzer.metadata['names']) - 30} 个\n"
            result += "\n"
            
        if 'consts' in self.binary_analyzer.metadata:
            result += "=== 常量 ===\n"
            for const in self.binary_analyzer.metadata['consts'][:20]:
                result += f"{repr(const)}\n"
            if len(self.binary_analyzer.metadata['consts']) > 20:
                result += f"... 还有 {len(self.binary_analyzer.metadata['consts']) - 20} 个\n"
            result += "\n"
        
        if not result:
            result = "无完整分析结果"
            
        self.complete_text.insert(tk.END, result)

    def display_binary_results(self):
        """显示二进制分析专用结果"""
        try:
            self.binary_text.delete('1.0', tk.END)
            
            if self.binary_analyzer:
                self._display_detailed_binary_results()
            else:
                self.binary_text.insert(tk.END, '请选择二进制文件分析模式...')
                
        except Exception as e:
            error_msg = f"显示二进制结果错误: {str(e)}\n"
            self.binary_text.delete('1.0', tk.END)
            self.binary_text.insert(tk.END, error_msg)

    def _display_detailed_binary_results(self):
        """显示详细的二进制分析结果"""
        result = ""
        
        # 显示字节码反汇编
        if self.binary_analyzer.bytecode_info:
            result += "=== 字节码反汇编 ===\n"
            result += f"{'偏移':<8} {'操作码':<20} {'参数':<8} {'描述'}\n"
            result += "-" * 60 + "\n"
            
            for instr in self.binary_analyzer.bytecode_info[:100]:
                offset = f"{instr['offset']:<8}"
                opname = f"{instr['opname']:<20}"
                arg = f"{instr['arg'] or '':<8}" if instr['arg'] is not None else f"{'':<8}"
                desc = f"{instr['argrepr']}"
                line_info = f" (行 {instr['lineno']})" if instr['lineno'] else ""
                
                result += f"{offset}{opname}{arg}{desc}{line_info}\n"
            
            if len(self.binary_analyzer.bytecode_info) > 100:
                result += f"\n... 还有 {len(self.binary_analyzer.bytecode_info) - 100} 条指令\n"
            result += "\n"
        
        # 显示文件头信息
        if self.binary_analyzer.metadata:
            if 'header_hex' in self.binary_analyzer.metadata:
                result += "=== 文件头十六进制 ===\n"
                header_hex = self.binary_analyzer.metadata['header_hex']
                # 格式化十六进制显示
                for i in range(0, len(header_hex), 32):
                    line = header_hex[i:i+32]
                    result += f"{i//2:04x}: "
                    # 每两个字符(一个字节)用空格分隔
                    for j in range(0, len(line), 2):
                        result += f"{line[j:j+2]} "
                    result += "\n"
                result += "\n"
        
        if not result:
            result = "无二进制分析结果"
            
        self.binary_text.insert(tk.END, result)

    def display_errors(self):
        try:
            self.error_text.delete('1.0', tk.END)
            
            errors = []
            if self.analyzer and self.analyzer.errors:
                errors.extend(self.analyzer.errors)
            if self.binary_analyzer and self.binary_analyzer.errors:
                errors.extend(self.binary_analyzer.errors)
                
            if errors:
                for error in errors:
                    self.error_text.insert(tk.END, f"{error}\n")
                self.error_text.insert(tk.END, f"\n总共 {len(errors)} 个错误")
            else:
                self.error_text.insert(tk.END, '分析过程中未发现错误。')
        except Exception as e:
            error_msg = f"显示错误信息错误: {str(e)}\n"
            self.error_text.delete('1.0', tk.END)
            self.error_text.insert(tk.END, error_msg)

    def add_jump_links(self, text_widget):
        """为文本中的跳转链接添加事件处理"""
        try:
            content = text_widget.get('1.0', tk.END)
            lines = content.split('\n')
            
            # 为跳转到定义行的链接添加事件
            current_line = 1
            for line in lines:
                if '[跳转到行' in line:
                    # 找到行号
                    import re
                    match = re.search(r'跳转到行 (\d+)', line)
                    if match:
                        line_num = int(match.group(1))
                        start_pos = f"{current_line}.{line.find('[跳转到行')}"
                        end_pos = f"{current_line}.{line.find(']', line.find('[跳转到行')) + 1}"
                        tag_name = f"jump_{current_line}_{line_num}"
                        text_widget.tag_add(tag_name, start_pos, end_pos)
                        text_widget.tag_config(tag_name, foreground="blue", underline=True)
                        # 使用默认参数捕获 line_num 的当前值
                        text_widget.tag_bind(tag_name, "<Button-1>", lambda e, ln=line_num: self.goto_line(ln))
                        text_widget.tag_bind(tag_name, "<Enter>", lambda e, tag=tag_name: text_widget.tag_config(tag, foreground="red"))
                        text_widget.tag_bind(tag_name, "<Leave>", lambda e, tag=tag_name: text_widget.tag_config(tag, foreground="blue"))
                
                elif '[跳转]' in line:
                    # 找到行号（从前面的内容中解析）
                    line_parts = line.split()
                    line_num = None
                    for part in line_parts:
                        if '行' in part:
                            # 尝试提取数字部分
                            num_part = ''.join(filter(str.isdigit, part))
                            if num_part:
                                line_num = int(num_part)
                                break
                    
                    if line_num:
                        start_pos = f"{current_line}.{line.find('[跳转]')}"
                        end_pos = f"{current_line}.{line.find(']', line.find('[跳转')) + 1}"
                        tag_name = f"jump_{current_line}_{line_num}"
                        text_widget.tag_add(tag_name, start_pos, end_pos)
                        text_widget.tag_config(tag_name, foreground="blue", underline=True)
                        # 修复：使用默认参数捕获 line_num 的当前值
                        text_widget.tag_bind(tag_name, "<Button-1>", lambda e, ln=line_num: self.goto_line(ln))
                        text_widget.tag_bind(tag_name, "<Enter>", lambda e, tag=tag_name: text_widget.tag_config(tag, foreground="red"))
                        text_widget.tag_bind(tag_name, "<Leave>", lambda e, tag=tag_name: text_widget.tag_config(tag, foreground="blue"))
                
                current_line += 1
                
        except Exception as e:
            print(f"添加跳转链接错误: {e}")

def handle_exception(exc_type, exc_value, exc_traceback):
    """全局异常处理"""
    if issubclass(exc_type, KeyboardInterrupt):
        sys.__excepthook__(exc_type, exc_value, exc_traceback)
        return
    
    error_msg = f"程序错误: {exc_type.__name__}: {exc_value}"
    print(error_msg)
    traceback.print_exc()

# 设置全局异常处理
sys.excepthook = handle_exception

def main():
    try:
        root = tk.Tk()
        app = CodeAnalyzerGUI(root)
        
        def on_closing():
            try:
                root.destroy()
            except:
                pass
        
        root.protocol("WM_DELETE_WINDOW", on_closing)
        root.mainloop()
        
    except Exception as e:
        print(f"程序启动失败: {e}")
        traceback.print_exc()
        input("按回车键退出...")

if __name__ == "__main__":
    main()
