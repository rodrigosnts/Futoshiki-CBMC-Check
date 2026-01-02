# Futoshiki-CBMC-Check

This project is related to the Segurança e Fiabilidade de Software (Security and Reliability of Software) course, from the 2nd cicle of Computer Science in Universidade da Beira Interior.

It's goal involves the use of **CBMC (C Bounded Model Checker)** to formally validate Futoshiki puzzle boards through the application of logical and structural constraints.

We model the rules of the Futoshiki board (value domains, row and column uniqueness, inequality constraints, and fixed values) and verify their correctness using **formal verification techniques** provided by CBMC.

This project was developed by the group members:
- Rodrigo Santos
- Marcos Assunção
- Enrico Nunes

## About

#### CBMC

CBMC is a formal verification tool for C and C++ programs, that analyses a program by **exploring all possible executions** up to a given bound, checking properties such as memory safety, absence of undefined behavior, and user‑defined assertions. This makes it useful for detecting issues like **invalid pointer usage**, **out‑of‑bounds array access**, or **violations of logical constraints**.
For more info, visit: 

https://www.cprover.org/cbmc/

#### Futoshiki

Futoshiki is a Japanese logic puzzle played on an **N×N**  grid (similar to Sudoku). The goal is to fill the board with the numbers **1 through N** so that each row and column contains all digits **exactly once**. What distinguishes Futoshiki from similar puzzles is the presence of inequality signs between adjacent cells. This includes that one value must be greater or smaller than its adjacent and that some cells may start with predefined numbers. Solving the puzzle involves combining these **inequality constraints** with **logic techniques** to progressively eliminate impossible values and narrow down the valid solution.
For more info, visit:

https://wikipedia.org/wiki/Futoshiki


## Requirements

To run the model checker, **CBMC** is required. Local installation is possible, however, for this project we used CBMC  via **Docker**. 

### Using CBMC with Docker 

Before getting started, ensure that Docker is installed and test the `cbmc` command :

```bash
docker run -it diffblue/cbmc:6.5.0 
```
The output should be similar to:
```bash
CBMC version 6.5.0 (n/a) 64-bit x86_64 linux
Please provide a program to verify
```
### Installing CBMC on your own machine (alternative)

Alternatively, CBMC can be installed locally.  
Binaries and installation instructions for Linux, macOS, and Windows are available at:

http://www.cprover.org/cbmc/

After installation, verify that CBMC is correctly installed by running: `cbmc`

## Running CBMC
To run CBMC and verify the program, run the command: `cbmc futoshiki.c`

## Expected Output

### Base Implementation
With the first implementation of the code, it's expected to get the following output:
```bash
** 1 of 83 failed (2 iterations) 
VERIFICATION FAILED. 
```
This happens because at the time, we manually declared the  ```__CPROVER_nondet_int``` function, allowing CBMC to look at it as a regular function. Therefore it treats it as a normal function and expects a function body, which leads to an internal verification failure. This doesn't mean the checker is failing the validations defined (the other 82 checks were successful), but that one internal failure of CBMC itself can cause a verification to fail. 
This issue is resolved in later versions by correctly declaring the function as `extern`.

### Universal Assertions
After introducing universal assertions with `__CPROVER_forall`, the expected output becomes:
```bash
** 0 of 125 failed (1 iterations) 
VERIFICATION SUCCESSFUL.
```

### Code Contracts
After restructuring the code and adding function‑level contracts using `__CPROVER_ensures`, the expected output becomes:
```bash
 ** 0 of 212 failed (1 iterations)
 VERIFICATION SUCCESSFUL
```
