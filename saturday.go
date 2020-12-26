package saturday

import (
	"fmt"
	"sort"
	"strings"
)

type solver struct {
	origVars []int

	assignments []assnVal
	watches     [][]int // watch literals (one for each literal; len is 2*len(assignments))

	unassigned      []int // unassigned vars (indexes into assignments; unordered)
	unassignedIndex []int // index of each var in unassigned (or -1)

	decisions    []decision // assigned vars from decision
	implications []literal  // implied literals from decisions & further implications
	propIndex    int        // index of the first un-propagated implication

	clauses []clause

	bcpBuf []literal

	numDecisions    int64
	numImplications int64
}

type clause struct {
	watches [2]literal
	lits    []literal
}

const verbose = false

func newSolver(cnf [][]int) *solver {
	sv := new(solver)
	vars := make(map[int]int)
	for _, cls := range cnf {
		for _, v := range cls {
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
	sv.watches = make([][]int, len(sv.origVars)*2)
	sv.clauses = make([]clause, len(cnf))
	for i, cls := range cnf {
		var watchesAdded int
		// Detect and delete duplicates.
		seen := make(map[literal]struct{}, len(cls))
		for _, v := range cls {
			neg := false
			if v < 0 {
				neg = true
				v = -v
			}
			lit := literal(vars[v]) << 1
			if neg {
				lit ^= 1
			}
			if _, ok := seen[lit]; ok {
				continue
			}
			seen[lit] = struct{}{}
			sv.clauses[i].lits = append(sv.clauses[i].lits, lit)
			if watchesAdded < 2 {
				sv.watches[lit] = append(sv.watches[lit], i)
				sv.clauses[i].watches[watchesAdded] = lit
				watchesAdded++
			}
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

const litNone literal = 1<<32 - 1

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
	// Handle empty clauses separately so we can assume there aren't any in
	// the main solve routines.
	for _, cls := range sv.clauses {
		if len(cls.lits) == 0 {
			return false
		}
	}

	for {
		if verbose {
			fmt.Println("solve loop", sv.unassigned)
		}
		v, ok := sv.popUnassigned()
		if !ok {
			return true
		}
		// Decide: set a var to true.
		sv.assignments[v] = assnTrue
		sv.numDecisions++
		if verbose {
			fmt.Printf("assigning %d->true | %s\n", sv.origVars[v], sv.stateString())
		}
		sv.decisions = append(sv.decisions, decision{
			implicationIdx: len(sv.implications),
			v:              v,
		})
		sv.propIndex = len(sv.implications)
		sv.implications = append(sv.implications, literal(v<<1))

		for !sv.bcp() {
			if !sv.resolveConflict() {
				return false
			}
		}
	}
}

func intsContain(s []int, n int) bool {
	for _, n1 := range s {
		if n1 == n {
			return true
		}
	}
	return false
}

// bcp carries out boolean constraint propagation (BCP) which finds all the
// direct implications of the current variable state. It returns true once there
// are no more implications to be made or false if it locates a conflict.
func (sv *solver) bcp() bool {
	for {
		imps := sv.implications[sv.propIndex:]
		if verbose {
			fmt.Printf("  bcp loop | %s\n", sv.stateString())
		}
		if len(imps) == 0 {
			// No implications left to propagate.
			if verbose {
				fmt.Println("  no more implications")
			}
			return true
		}
		sv.propIndex = len(sv.implications)
		for _, impliedLit := range imps {
			neg := impliedLit ^ 1
			if verbose {
				fmt.Printf("  checking impl %d by visiting watches for %d\n",
					sv.origLit(impliedLit), sv.origLit(neg))
			}
			watches := sv.watches[neg]
		watchesLoop:
			for i := 0; i < len(watches); {
				clauseIdx := watches[i]
				cls := sv.clauses[clauseIdx]
				otherWatch := cls.watches[0]
				if otherWatch == neg {
					otherWatch = cls.watches[1]
				}
				state := assnFalse
				for _, lit := range cls.lits {
					if lit == neg {
						continue
					}
					assn := lit.assn()
					v := int(lit >> 1)
					switch sv.assignments[v] {
					case unassigned:
						if state == assnFalse {
							state = unassigned
						}
					case assn:
						state = assnTrue
					default:
						// Literal is false already.
						continue
					}
					if lit == otherWatch {
						continue
					}
					// We know that lit is available to become the replacement
					// watch literal.
					sv.watches[lit] = append(sv.watches[lit], clauseIdx)
					// Remove from the neg watch list.
					watches[i], watches[len(watches)-1] = watches[len(watches)-1], watches[i]
					watches = watches[:len(watches)-1]
					sv.watches[neg] = watches
					sv.clauses[clauseIdx].watches = [2]literal{lit, otherWatch}
					continue watchesLoop
				}
				i++
				switch state {
				case assnTrue:
					// Clause is satisified already; nothing to do.
					continue
				case assnFalse:
					// No satisfiable literals in this clause: conflict.
					if verbose {
						fmt.Printf("  conflict at clause %d\n", clauseIdx)
					}
					return false
				}
				// This is now a unit clause and the other watch literal is implied.
				v := int(otherWatch >> 1)
				if verbose {
					fmt.Printf("  clause %d is unit (imp: %d)\n", clauseIdx, sv.origLit(otherWatch))
				}
				if sv.assignments[v] == unassigned {
					if verbose {
						fmt.Printf("    assigning to %s\n", otherWatch.assn())
					}
					sv.assignments[v] = otherWatch.assn()
					sv.deleteUnassigned(v)
					sv.numImplications++
					sv.implications = append(sv.implications, otherWatch)
				}
			}
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
		fmt.Fprintf(&b, "%s%d:%c", s, sv.origVars[i], assn.String()[0])
	}
	b.WriteString("} watch: {")
	for lit, watches := range sv.watches {
		var s string
		if lit > 0 {
			s = ", "
		}
		fmt.Fprintf(&b, "%s%d->%v", s, sv.origLit(literal(lit)), watches)
	}
	b.WriteString("}")
	return b.String()
}

func (sv *solver) origLit(lit literal) int {
	x := sv.origVars[lit>>1]
	if lit&1 == 1 {
		return -x
	}
	return x
}

// resolveConflict tries to fix the current conflict by flipping the most
// recently made decision.
func (sv *solver) resolveConflict() bool {
	if verbose {
		fmt.Println("  resolveConflict")
	}
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
	if verbose {
		fmt.Printf("  assigning %d->false | %s\n", sv.origVars[d.v], sv.stateString())
	}
	for i := len(sv.implications) - 1; i > d.implicationIdx; i-- {
		v := int(sv.implications[i] >> 1)
		sv.addUnassigned(v)
		sv.assignments[v] = unassigned
	}
	sv.implications = sv.implications[:d.implicationIdx+1]
	sv.implications[len(sv.implications)-1] ^= 1
	sv.decisions = sv.decisions[:di+1]
	sv.assignments[d.v] = assnFalse
	sv.propIndex = d.implicationIdx
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
