import os
content = '''format_version: '2.0'
input_files: '%s'
properties:
  - property_file: ../properties/unreach-call.prp
    expected_verdict: true

options:
  language: C
  data_model: ILP32
'''

bench_dir = './benchmark/sv-benchmarks-main-c-nla-digbench/c/nla-digbench'
for filename in os.listdir(bench_dir):
    if filename.endswith('.c'):
        yml_name = os.path.join(os.path.splitext(filename)[0] + '.yml')
        full_name = os.path.join(bench_dir, yml_name)
        with open(full_name, 'w') as fp:
            fp.write(content % filename)