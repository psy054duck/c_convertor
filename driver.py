import subprocess
import sys
import os
import z3
def main():
    tool_name = 'build/main'
    filename = 'test/test.c'
    target = 'test/test.ll'
    cmd = ['clang', '-emit-llvm', '-S' , '-Xclang', '-disable-O0-optnone', filename, '-o', target]
    tmp_path = 'tmp/'
    is_success = subprocess.run(cmd)
    if not is_success:
        print('Fail to convert %s into LLVM IR' % filename)
        exit(0)
    cmd = [tool_name, target]
    try:
        print(subprocess.check_output(cmd).decode())
    except subprocess.TimeoutExpired:
        pass
    for smt_filename in [os.path.join(tmp_path, i) for i in os.listdir(tmp_path) if i.endswith('.smt2')]:
        formulas = z3.parse_smt2_file(smt_filename)
        print('*'*50)
        for f in formulas:
            print(z3.simplify(f))


if __name__ == '__main__':
    main()
