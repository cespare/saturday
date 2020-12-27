# Saturday

[![Go Reference](https://pkg.go.dev/badge/github.com/cespare/saturday.svg)](https://pkg.go.dev/github.com/cespare/saturday)

Saturday is a simple SAT solver in Go that implements the Davis-Putnam
backtracking algorithm plus a few optimizations as described in the 2001 paper
[*Chaff: Engineering an Efficient SAT Solver*][chaff].

In particular, Saturday uses the following techniques:

* Boolean constraint propagation (equivalent to the "unit propagation" procedure
  described in the recent literature)
* Two-variable watch lists

TODO (perhaps):

* Clause learning + deletion
* Some kind of decision heuristic
* Better simplification

[chaff]: http://www.princeton.edu/~chaff/publication/DAC2001v56.pdf

## Example

Suppose we want to determine whether the boolean formula

    (¬x ∨ y) ∧ (¬y ∨ z) ∧ (x ∨ ¬z ∨ y)

is satisfiable. The first step is to encode this formula using integers starting
with 1. Boolean negation will be indicated with integer negation. So `x` becomes
`1`, `¬y` becomes `-2`, and so forth:

    [[-1, 2], [-2, 3], [1, -3, 2]]

Then we can call `saturday.Solve` to determine whether the problem is
satisfiable and obtain an example assignment if it is:

```
problem := [][]int{{-1, 2}, {-2, 3}, {1, -3, 2}}
solution, ok := saturday.Solve(problem)
if !ok {
	fmt.Println("not satisfiable")
	return
}
fmt.Println("satisfiable:", solution)
```

This prints that the problem is satisfiable and emits some solution:

    satisfiable: [-1 2 3]

## CLI tool

There is a small CLI tool in cmd/saturday which reads problems in the
conventional DIMACS CNF format and solves them. It prints SAT and a satisfying
assignment if the problem is satisfiable and UNSAT otherwise.

```
$ cat >problem.cnf
c Saturday example
p cnf 3 3
-1 2 0
-2 3 0
1 -3 2 0
$ saturday problem.cnf
SAT
-1 2 3
```

Run `saturday -h` for more info.
