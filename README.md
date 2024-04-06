## Introduction
This is a prototype tool that implements our two works on multi-path loop analysis using recurrence analysis techniques.
Those two works are directly used in program verification.

This tool consists of two parts:
  - The front end converts the input c program into llvm ir and then translates the ir into first order logic that can be consumed by Z3.
  It also extract recurrences from loops and feeds them into the second part, recurrence solver, for closed-form solutions to either individual variables or expressions among them. These closed-form solutions are also provided to Z3.
  - The recurrence solver implements our proposed methods:
    - Solving conditional linear recurrences: by identifying a periodic properties exhibited in some conditional recurrences, we proposed an approach to compute closed-form solutions to them.
    The closed-form solutions are of a case-by-case form so it indeed computes disjunctive properties.
    - Finding polynomial expressions satisfying c-finite recurrences: when the first approach fails to compute closed-form solutions to individual variables, the recurrence solver resorts to finding polynomial expressions among them satisfying some c-finite recurrences.
    Closed-form solutions to them are computed using standard methods for solving c-finite recurrences.

## Dependencies
- All python dependencies are summarized in the file `requirements.txt`.
  One can install all of them using the following command
  ```
  pip install -r requirements.txt
  ```
- LLVM 16.0.6. One can build it following the instruction from the official website (https://llvm.org/docs/CMake.html).
- Z3 4.12.2.0. One can also build it following its official instruction (https://github.com/Z3Prover/z3/blob/master/README-CMake.md)

## Build it with CMake
Once all dependencies are ready, this tool can be built using the following command:
```
mkdir build
cd build
cmake ..
make
```
After tens of seconds, the tool can be built successfully.

## Usage
After building, go back to the root of the source tree.
To use this tool, one can enter command of the following form
```
python driver.py filename
```
For example, if one wants to prove the program `benchmark/sv-benchmarks-main-c-nla-digbench/c/nla-split/prod4br-ll1.c`, then one can type the following command:
```
python driver.py benchmark/sv-benchmarks-main-c-nla-digbench/c/nla-split/prod4br-ll1.c
```
After a few seconds, it should respond with `correct`, which means it prove the assertion in `prod4br-ll1.c` successfully.

More concretely,
there are three types of responses:
  - `correct` stands for a correct assertion.
  - `wrong` stands for a wrong assertion.
  - `unknown` means that the tool is not able to tell whether the assertion is correct or not.

## Related Publications
On Polynomial Expressions with C-Finite Recurrences in Loops with Nested Nondeterministic Branches (To appear in CAV 2024)

Solving Conditional Linear Recurrences for Program Verification: The Periodic Case (OOPSLA 2023)
