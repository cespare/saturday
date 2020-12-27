package saturday

import (
	"fmt"
	"math/rand"
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

func TestRandomized(t *testing.T) {
	for _, tt := range []struct {
		numVars    int
		numClauses int
		numSeeds   int
	}{
		{2, 2, 10},
		{3, 10, 100},
		{5, 10, 1000},
		{10, 20, 1000},
	} {
		name := fmt.Sprintf("vars=%d,clauses=%d", tt.numVars, tt.numClauses)
		t.Run(name, func(t *testing.T) {
			for seed := 0; seed < tt.numSeeds; seed++ {
				problem := makeRandomSat(int64(seed), tt.numVars, tt.numClauses)
				var b strings.Builder
				if err := WriteDIMACS(&b, problem); err != nil {
					panic(err)
				}
				text := b.String()
				soln, ok := Solve(problem)
				if !ok {
					t.Fatalf("[seed=%d] got UNSAT:\n\n%s\n", seed, text)
				}
				if !solutionIsValid(problem, soln) {
					t.Fatalf("[seed=%d] got incorrect solution:\n\n%v\n\n%s\n",
						seed, soln, text)
				}
			}
		})
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
	if !solutionIsValid(problem, soln) {
		t.Fatalf("got assignment %v, but it is not a solution to this SAT problem", soln)
	}
}

func solutionIsValid(problem [][]int, soln []int) bool {
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
		return false
	}
	return true
}

func testFixtureUnsat(t *testing.T, problem [][]int) {
	soln, ok := Solve(problem)
	if ok {
		t.Fatalf("got SAT with assignment %v; expected UNSAT", soln)
	}
}

func makeRandomSat(seed int64, numVars, numClauses int) [][]int {
	rng := rand.New(rand.NewSource(seed))
	assignment := make([]bool, numVars)
	for v := range assignment {
		if rng.Intn(2) == 1 {
			assignment[v] = true
		}
	}
	vars := make([]int, numVars)
	for v := range vars {
		vars[v] = v
	}
	problem := make([][]int, numClauses)
	for i := range problem {
		rng.Shuffle(len(vars), func(i, j int) {
			vars[i], vars[j] = vars[j], vars[i]
		})
		problem[i] = make([]int, rng.Intn(numVars)+1)
		fixed := rng.Intn(len(problem[i])) // pick one literal to match assignment
		for j := range problem[i] {
			v := vars[j] + 1
			if j == fixed {
				if !assignment[v-1] {
					v = -v
				}
			} else {
				if rng.Intn(2) == 1 {
					v = -v
				}
			}
			problem[i][j] = v
		}
	}
	// Remap vars to a contiguous set in [1, n] (where n is the number of
	// vars we actually ended up using).
	remap := make(map[int]int)
	for _, cls := range problem {
		for i, v := range cls {
			neg := false
			if v < 0 {
				neg = true
				v = -v
			}
			if x, ok := remap[v]; ok {
				v = x
			} else {
				x := len(remap) + 1
				remap[v] = x
				v = x
			}
			if neg {
				v = -v
			}
			cls[i] = v
		}
	}
	return problem
}
