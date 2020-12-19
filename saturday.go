package saturday

import (
	"fmt"
	"sort"
	"strings"
)

type solver struct {
	origVars []int

	assignments []assnVal

	unassigned      []int // unassigned vars (indexes into assignments; unordered)
	unassignedIndex []int // index of each var in unassigned (or -1)

	decisions    []decision // assigned vars from decision
	implications []int      // assigned vars from decisions & further implications

	clauses [][]literal

	bcpBuf []literal

	numDecisions    int64
	numImplications int64
}

func newSolver(cnf [][]int) *solver {
	sv := new(solver)
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
				sv.origVars = append(sv.origVars, v)
				vars[v] = 0
			}
		}
	}
	sort.Ints(sv.origVars)
	for i, v := range sv.origVars {
		vars[v] = i
	}
	sv.unassigned = make([]int, len(sv.origVars))
	sv.unassignedIndex = make([]int, len(sv.origVars))
	for i := range sv.unassigned {
		sv.unassigned[i] = len(sv.origVars) - i - 1
		sv.unassignedIndex[i] = len(sv.origVars) - i - 1
	}
	sv.assignments = make([]assnVal, len(sv.origVars))
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
	return sv
}

func Solve(cnf [][]int) ([]int, bool) {
	sv := newSolver(cnf)
	if !sv.solve() {
		return nil, false
	}

	for i, assn := range sv.assignments {
		switch assn {
		case assnFalse:
			sv.origVars[i] *= -1
		case assnTrue:
		default:
			panic("incomplete solution")
		}
	}
	return sv.origVars, true
}

// A literal represents an instance of a variable or its negation in a clause.
// The value is 2 times the variable value (index) or 2x+1 for negation.
type literal uint32

func (l literal) assn() assnVal {
	return assnVal(l&1) + 1
}

type assnVal uint8

const (
	unassigned assnVal = 0
	assnTrue   assnVal = 1
	assnFalse  assnVal = 2
)

// func (a assnVal) inv() assnVal { return a ^ 3 }

func (a assnVal) String() string {
	switch a {
	case unassigned:
		return "unassigned"
	case assnTrue:
		return "true"
	case assnFalse:
		return "false"
	default:
		panic("unreached")
	}
}

type decision struct {
	implicationIdx int
	v              int
}

func (sv *solver) solve() bool {
	for {
		// fmt.Println("solve loop")
		v, ok := sv.popUnassigned()
		if !ok {
			return true
		}
		// Decide: set a var to true.
		sv.assignments[v] = assnTrue
		sv.numDecisions++
		// fmt.Printf("assigning %d to true | %s\n", v, sv.stateString())
		sv.decisions = append(sv.decisions, decision{
			implicationIdx: len(sv.implications),
			v:              v,
		})
		sv.implications = append(sv.implications, v)

		// sv.bcpCount++
		// if sv.bcpCount > 1000 {
		// 	return false
		// }

		for !sv.bcp() {
			if !sv.resolveConflict() {
				return false
			}
		}
	}
}

// bcp carries out boolean constraint propagation (BCP) which finds all the
// direct implications of the current variable state. It returns true once there
// are no more implications to be made or false if it locates a conflict.
func (sv *solver) bcp() bool {
	for {
		// fmt.Println("  bcp loop")
		sv.bcpBuf = sv.bcpBuf[:0]
	cnfLoop:
		for _, clause := range sv.clauses {
			foundUnassigned := false
			var lit literal
		clauseLoop:
			for _, lit1 := range clause {
				v := int(lit1 >> 1)
				assn := sv.assignments[v]
				// if i == 9 {
				// fmt.Printf("  i=%d, v=%d; lit1=%d; assn=%s\n", i, v, lit1, assn)
				// }
				if assn == unassigned {
					if foundUnassigned {
						// Multiple unassigned; not unit.
						continue cnfLoop
					}
					lit = lit1
					foundUnassigned = true
					continue clauseLoop
				}
				if lit1.assn() == assn {
					// Clause already satisfied.
					continue cnfLoop
				}
			}
			if !foundUnassigned {
				// Conflict.
				// fmt.Print("  conflict!")
				return false
			}
			// fmt.Printf("  unit clause at %d (lit=%d)\n", i, lit)
			// Found a unit clause.
			sv.bcpBuf = append(sv.bcpBuf, lit)
		}

		if len(sv.bcpBuf) == 0 {
			// No more implications.
			return true
		}

		for _, lit := range sv.bcpBuf {
			v := int(lit >> 1)
			assn := lit.assn()
			// If v is unassigned or matches lit already, good.
			// But if it is already assigned the inverse, we found a conflict.
			switch sv.assignments[v] {
			case unassigned:
			case assn:
				continue
			default:
				// fmt.Printf("  conflict on %d\n", v)
				return false
			}
			sv.assignments[v] = assn
			// fmt.Printf("  implication: %d is %s | %s\n", v, assn, sv.stateString())
			sv.deleteUnassigned(v)
			sv.numImplications++
			sv.implications = append(sv.implications, v)
		}
	}

}

func (sv *solver) stateString() string {
	var b strings.Builder
	b.WriteByte('{')
	for i, assn := range sv.assignments {
		var s string
		if i > 0 {
			s = ", "
		}
		fmt.Fprintf(&b, "%s%d:%c", s, i, assn.String()[0])
	}
	b.WriteByte('}')
	return b.String()
}

// resolveConflict tries to fix the current conflict by flipping the most
// recently made decision.
func (sv *solver) resolveConflict() bool {
	// fmt.Println("  resolveConflict")
	di := -1
	var d decision
	for i := len(sv.decisions) - 1; i >= 0; i-- {
		d = sv.decisions[i]
		if sv.assignments[d.v] == assnTrue {
			// d hasn't been tried both ways yet.
			di = i
			break
		}
	}
	if di == -1 {
		return false // not satisfiable
	}
	// Flip d from true to false and roll back the invalidated implications.
	sv.decisions = sv.decisions[:di+1]
	sv.assignments[d.v] = assnFalse
	// fmt.Printf("  assigning %d to false | %s\n", d.v, sv.stateString())
	for i := len(sv.implications) - 1; i > d.implicationIdx; i-- {
		v := sv.implications[i]
		sv.addUnassigned(v)
		sv.assignments[v] = unassigned
	}
	sv.implications = sv.implications[:d.implicationIdx+1]
	return true
}

func (sv *solver) popUnassigned() (int, bool) {
	if len(sv.unassigned) == 0 {
		return 0, false
	}
	v := sv.unassigned[len(sv.unassigned)-1]
	sv.unassigned = sv.unassigned[:len(sv.unassigned)-1]
	sv.unassignedIndex[v] = -1
	return v, true
}

func (sv *solver) deleteUnassigned(v int) {
	i := sv.unassignedIndex[v]
	last := sv.unassigned[len(sv.unassigned)-1]
	sv.unassigned[i] = last
	sv.unassigned = sv.unassigned[:len(sv.unassigned)-1]
	sv.unassignedIndex[last] = i // last may be v
	sv.unassignedIndex[v] = -1
}

func (sv *solver) addUnassigned(v int) {
	if sv.unassignedIndex[v] != -1 {
		panic("assigning already-assigned var")
	}
	sv.unassignedIndex[v] = len(sv.unassigned)
	sv.unassigned = append(sv.unassigned, v)
}
