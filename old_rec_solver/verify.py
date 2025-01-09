from cparser import check
import fire

def main(filename):
    res = str(check(filename, debug=False))
    if res == 'sat':
        print('Wrong')
    elif res == 'unsat':
        print('Correct')
    else:
        print('Unknown')

if __name__ == '__main__':
    fire.Fire(main)
