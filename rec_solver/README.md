# Conditional Recurrence Solver and Program Verifier
## Overview

The conditional recurrence solver tries to solve a conditional linear recurrence of the following form

![alt text](fig/1.png?raw=true)
The program verifier tries to verify the correctness of an assertion in a C program.

## 

## Dependencies

The program should be run with Python 3.

### Packages

* z3-solver (4.8.10.0)
* wolframclient (1.1.6)
* sympy (1.8)
* fire (0.4.0)
* ply (3.11)
* pyyaml (5.4.1)

All these packages can be install using the command `pip install xxx`, where `xxx` is the name of the packa listed above.

If one is using Anaconda, it recommended to run the following commands to get the python environment we used.

```bash
conda env update -f=env.yaml 
conda activate rec
```

### Mathematica

Go to https://www.wolfram.com/engine/?source=nav for downloading and installing Wolfram Engine. Once installed, replace the value of `MathematicaPath` in `config.json` with the path you installed the Wolfram Engine. Before running our program, please run the engine once to activate it.

## Usage

### Recurrence Solver

The recurrence should be put in a file using the language defined in the program. The following is an example and suppose that it is stored in a file called `recurrence.txt`.

```c
i = 0;
j = 0;
l = 0;

if (l % 2 == 0) {
  i = i + 1;
  j = j;
  l = l + 1;
} else {
  j = j + 1;
  i = i;
  l = l + 1;
}
```

Roughly speaking, the file has two parts. The first one is at the begining of the file for the initial values as the first three lines in the example. The second part is the recurrence, which stands for

<img src="fig/2.png" alt="example-recurrence" style="zoom:50%;" />

Note that, although the language is C-like, but the semantics is not the same. The assignments in each block are executed parallelly instead of sequentially. So if a recurrence is writen as `if (l < 10) { i = j; j = i;}`, the effect inside the pair of curly braces is swaping the values of `i` and `j`.

After running the following command

```bash
python rec_solver.py recurrence.txt
```

the program will output the following result

```bash
i(n) == If(Mod(n, 2) == 0, n, n + 1)
j(n) == If(Mod(n, 2) == 0, n, n - 1)
l(n) == If(Mod(n, 2) == 0, n, n)
```

which represents a closed-form solution to the recurrence

<img src="fig/3.png" alt="example closed-form" style="zoom:50%;" />

### Program Verifier

The field `timeout` in `config.json` represent the timeout in seconds.

Type the following command to run the verifier

```bash
python verify.py xxx.c
```

where `xxx.c` is the program to be verified.

As an example, suppose the following program is stored in `fsm.c`.

```c
int main() {
    int s = -5;
    int x1 = 0;
    int x2 = 0;
    int size = __VERIFIER_nondet_uint();
    while (x1 < size) {
        if (s == 1) {
            x1++;
            s++;
        } else if (s == 2) {
            x2++;
            s++;
        } else if (s == 4) {
            s = 1;
        } else {
            s++;
        }
        __VERIFIER_assert(s != 1 || (s == 1 && x1 == x2));
    }
}
```

After running the following command

```bash
python verify.py fsm.c
```

the program will output

```bash
Correct
```

which means the assertion in Line 18 is correct.

Other possible output are `Wrong` for unsafe assertion, and `Unknown` for failing to prove or disprove.
