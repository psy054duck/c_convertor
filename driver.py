import subprocess
import sys
import os
import z3
import fire
def run(filename):
    tool_name = 'build/main'
    # filename = 'test/test.c'
    target = 'tmp/test.ll'
    cmd = ['clang', '-emit-llvm', '-S' , '-O0', '-Xclang', '-disable-O0-optnone', filename, '-o', target]
    tmp_path = 'tmp/'
    is_success = subprocess.run(cmd, timeout=60*5)
    if not is_success:
        print('Fail to convert %s into LLVM IR' % filename)
        exit(0)
    cmd = [tool_name, target]
    try:
        ans = subprocess.check_output(cmd, timeout=60*5, stderr=subprocess.DEVNULL).decode().strip()
        return ans
    # except subprocess.TimeoutExpired:
    except:
        return 'unknown'


if __name__ == '__main__':
    fire.Fire(run)
