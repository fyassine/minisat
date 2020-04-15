# minisat
a simple sat solver using **dpll** algorithm.
Based on the **olr** (one literal rule) and **plr** (plural literal), cnf clauses are processed accordingly.

## Getting Started
* create a *.cnf* file using the following standard format
```
1 -2 4 0
3 -4 0
2 0
```
* input the file path
* result will be either:
  * a satisfiable expression with the settings
  * a not satisfiable expression
