package saturday

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestFixtures(t *testing.T) {
	filenames, err := filepath.Glob("testdata/*.cnf")
	if err != nil {
		t.Fatal(err)
	}
	for _, filename := range filenames {
		f, err := os.Open(filename)
		if err != nil {
			t.Fatal(err)
		}
		problem, err := ParseDIMACS(f)
		f.Close()
		if err != nil {
			t.Fatalf("bad fixture %s: %s", filename, err)
		}
		name := filepath.Base(filename)
		switch {
		case strings.HasSuffix(filename, ".sat.cnf"):
			t.Run(name, func(t *testing.T) { testFixtureSat(t, problem) })
		case strings.HasSuffix(filename, ".unsat.cnf"):
			t.Run(name, func(t *testing.T) { testFixtureUnsat(t, problem) })
		default:
			t.Fatalf("bad testdata CNF filename: %q", filename)
		}
	}
}

func testFixtureSat(t *testing.T, problem [][]int) {
	soln, ok := Solve(problem)
	if !ok {
		t.Fatalf("got UNSAT; want SAT")
	}
	vars := make(map[int]bool)
	for _, v := range soln {
		if v < 0 {
			vars[-v] = false
			vars[v] = true
		} else {
			vars[v] = true
			vars[-v] = false
		}
	}
clauseLoop:
	for _, clause := range problem {
		for _, v := range clause {
			if vars[v] {
				continue clauseLoop
			}
		}
		t.Fatalf("got assignment %v, but it is not a solution to this SAT problem", soln)
	}
}

func testFixtureUnsat(t *testing.T, problem [][]int) {
	soln, ok := Solve(problem)
	if ok {
		t.Fatalf("got SAT with assignment %v; expected UNSAT", soln)
	}
}
