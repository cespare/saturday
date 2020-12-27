package main

import (
	"flag"
	"fmt"
	"io"
	"log"
	"os"
	"sort"

	"github.com/cespare/saturday"
)

func main() {
	log.SetFlags(0)
	verbose := flag.Bool("v", false, "verbose mode")
	flag.Usage = func() {
		fmt.Fprint(os.Stderr, `Saturday: a toy SAT solver.

Usage:

  saturday [-v] [input.cnf]

Saturday reads a single problem specification in the DIMACS CNF format.
It writes the output in the conventional way: either the first line is UNSAT,
or else the first line is SAT and the second line gives the assignments in the
same format as an input clause.

If no input file is given, saturday reads from standard input.

The -v flag controls verbose output.
`)
	}
	flag.Parse()

	var r io.Reader = os.Stdin
	if flag.NArg() >= 1 {
		f, err := os.Open(flag.Arg(0))
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

	soln, stats, ok := saturday.Solve(cnf)
	if *verbose {
		var keys []string
		var maxKeyLen int
		for key := range stats {
			keys = append(keys, key)
			if len(key) > maxKeyLen {
				maxKeyLen = len(key)
			}
		}
		sort.Strings(keys)
		for _, key := range keys {
			fmt.Fprintf(os.Stderr, "%*s %v\n", maxKeyLen, key, stats[key])
		}
	}
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
