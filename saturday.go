package saturday

import "sort"

type solver struct {
	assignments []assnVal
	clauses     [][]literal
}

func Solve(cnf [][]int) ([]int, bool) {
	var origVars []int
	var sv solver
	vars := make(map[int]int)
	for _, clause := range cnf {
		for _, v := range clause {
			if v == 0 {
				panic("zero value passed to Solve")
			}
			if v < 0 {
				v = -v
			}
			if _, ok := vars[v]; !ok {
				origVars = append(origVars, v)
				vars[v] = 0
			}
		}
	}
	sort.Ints(origVars)
	for i, v := range origVars {
		vars[v] = i
	}
	sv.assignments = make([]assnVal, len(origVars))
	sv.clauses = make([][]literal, len(cnf))
	for i, clause := range cnf {
		sv.clauses[i] = make([]literal, len(clause))
		for j, v := range clause {
			neg := false
			if v < 0 {
				neg = true
				v = -v
			}
			lit := literal(vars[v]) << 1
			if neg {
				lit ^= 1
			}
			sv.clauses[i][j] = lit
		}
	}

	if !sv.solve() {
		return nil, false
	}

	for i, assn := range sv.assignments {
		switch assn {
		case assnFalse:
			origVars[i] *= -1
		case assnTrue:
		default:
			panic("incomplete solution")
		}
	}
	return origVars, true
}

func (sv *solver) solve() bool {
	for i := range sv.assignments {
		if i == 1 {
			sv.assignments[i] = assnFalse
		} else {
			sv.assignments[i] = assnFalse
		}
	}
	return true
}

// A literal represents an instance of a variable or its negation in a clause.
// The value is 2 times the variable value (index) or 2x+1 for negation.
type literal uint32

type assnVal uint8

const (
	unassigned assnVal = iota
	assnFalse
	assnTrue
)
