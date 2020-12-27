package saturday

import "fmt"

func ExampleSolve() {
	// Problem: (¬x ∨ y) ∧ (¬y ∨ z) ∧ (x ∨ ¬z ∨ y) ∧ y

	// First, encode this using integers.
	problem := [][]int{
		{-1, -2},
		{-2, 3},
		{1, -3, 2},
		{2},
	}

	// Next, call Solve to see if the problem is satisfiable and, if so,
	// what a satisfying assignment is.
	solution, _, ok := Solve(problem)
	if !ok {
		fmt.Println("not satisfiable")
		return
	}
	fmt.Println("satisfiable:", solution)
	// Output: satisfiable: [-1 2 3]
}
