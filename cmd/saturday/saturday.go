package main

import (
	"fmt"
	"io"
	"log"
	"os"

	"github.com/cespare/saturday"
)

func main() {
	log.SetFlags(0)
	var r io.Reader = os.Stdin
	if len(os.Args) > 1 {
		switch os.Args[1] {
		case "-h", "help", "-help", "--help":
			fmt.Print(`Saturday: a toy SAT solver.

Usage:

  saturday [input.cnf]

Saturday reads a single problem specification in the DIMACS CNF format.
It writes the output in the conventional way: either the first line is UNSAT,
or else the first line is SAT and the second line gives the assignments in the
same format as an input clause.

If no input file is given, saturday reads from standard input.
`)
			os.Exit(2)
		}
		f, err := os.Open(os.Args[1])
		if err != nil {
			log.Fatal(err)
		}
		defer f.Close()
		r = f
	}

	cnf, err := saturday.ParseDIMACS(r)
	if err != nil {
		log.Fatalln("Error reading input file as DIMACS CNF:", err)
	}

	soln, ok := saturday.Solve(cnf)
	if !ok {
		fmt.Println("UNSAT")
		return
	}
	fmt.Println("SAT")
	for i, v := range soln {
		if i > 0 {
			fmt.Print(" ")
		}
		fmt.Print(v)
	}
	fmt.Println()
}
