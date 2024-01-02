import os
from driver import run  

def main():
    benchmark_dir = 'benchmark/sv-benchmarks-main-c-nla-digbench/c/nla-split'
    filenames = sorted(os.listdir(benchmark_dir))
    max_len = max([len(filename) for filename in filenames])
    tot = 0
    tot_correct = 0
    for filename in filenames:
        if filename.endswith('.c'):
            tot += 1
            full_path = os.path.join(benchmark_dir, filename)
            ans = run(full_path)
            if ans == 'correct': tot_correct += 1
            print('{name:{width}}{ans:10}{num_correct}/{tot}'.format(name=filename, width=max_len+10, ans=ans, num_correct=tot_correct, tot=tot))


if __name__ == '__main__':
    main()