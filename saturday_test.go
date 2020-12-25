package saturday

import (
	"os"
	"path/filepath"
	"strings"
	"testing"
)

func TestFixtures(t *testing.T) {
	for _, tt := range loadFixtures(t, false) {
		if tt.sat {
			t.Run(tt.name, func(t *testing.T) {
				testFixtureSat(t, tt.problem)
			})
		} else {
			t.Run(tt.name, func(t *testing.T) {
				testFixtureUnsat(t, tt.problem)
			})
		}
	}
}

func BenchmarkFixtures(b *testing.B) {
	for _, bb := range loadFixtures(b, true) {
		b.Run(bb.name, func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				sv := newSolver(bb.problem)
				sv.solve()
				b.ReportMetric(float64(sv.numDecisions), "decisions/op")
				b.ReportMetric(float64(sv.numImplications), "implications/op")
			}
		})
	}
}

type fixtureTest struct {
	name    string
	problem [][]int
	sat     bool
}

func loadFixtures(tb testing.TB, onlyBench bool) []fixtureTest {
	filenames, err := filepath.Glob("testdata/bench/*.cnf")
	if err != nil {
		tb.Fatal(err)
	}
	if !onlyBench {
		nonBench, err := filepath.Glob("testdata/*.cnf")
		if err != nil {
			tb.Fatal(err)
		}
		filenames = append(filenames, nonBench...)
	}
	var tests []fixtureTest
	for _, filename := range filenames {
		f, err := os.Open(filename)
		if err != nil {
			tb.Fatal(err)
		}
		problem, err := ParseDIMACS(f)
		f.Close()
		if err != nil {
			tb.Fatalf("bad fixture %s: %s", filename, err)
		}
		name := filepath.Base(filename)
		switch {
		case strings.HasSuffix(filename, ".sat.cnf"):
			tests = append(tests, fixtureTest{name, problem, true})
		case strings.HasSuffix(filename, ".unsat.cnf"):
			tests = append(tests, fixtureTest{name, problem, false})
		default:
			tb.Fatalf("bad testdata CNF filename: %q", filename)
		}
	}
	return tests
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
