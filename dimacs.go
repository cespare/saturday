package saturday

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"strconv"
	"strings"
)

// ParseDIMACS parses text in the DIMACS CNF format.
//
// For convenience, a few non-standard variations are accepted:
//
//   * Comments (lines beginning with 'c') may appear anywhere, not just in the
//     preamble.
//   * The problem line may be missing.
//
func ParseDIMACS(r io.Reader) ([][]int, error) {
	var problem struct {
		vars    int
		clauses int
	}
	var clauses [][]int
	var clause []int
	s := bufio.NewScanner(r)
	for s.Scan() {
		line := s.Text()
		if len(line) == 0 || line[0] == 'c' {
			continue
		}
		// Some CNF formats attach extra data in a trailer after a line
		// containing a single %.
		if line == "%" {
			break
		}
		if line[0] == 'p' {
			if len(clauses) > 0 {
				return nil, errors.New("problem line appears after clauses")
			}
			if problem.vars > 0 {
				return nil, errors.New("multiple problem lines")
			}
			fields := strings.Fields(line)
			if len(fields) != 4 {
				return nil, fmt.Errorf("malformed problem line %q", line)
			}
			if fields[0] != "p" {
				return nil, fmt.Errorf("problem line starts with unexpected signifier %q", fields[0])
			}
			if fields[1] != "cnf" {
				return nil, fmt.Errorf("only cnf supported; got %q", fields[1])
			}
			var err error
			problem.vars, err = strconv.Atoi(fields[2])
			if err != nil {
				return nil, fmt.Errorf("malformed #vars in problem line: %s", err)
			}
			problem.clauses, err = strconv.Atoi(fields[3])
			if err != nil {
				return nil, fmt.Errorf("malformed #clauses in problem line: %s", err)
			}
			if problem.vars < 0 {
				return nil, fmt.Errorf("invalid #vars %d", problem.vars)
			}
			if problem.clauses < 0 {
				return nil, fmt.Errorf("invalid #clauses %d", problem.clauses)
			}
			continue
		}
		for _, field := range strings.Fields(line) {
			n, err := strconv.Atoi(field)
			if err != nil {
				return nil, fmt.Errorf("invalid variable: %s", err)
			}
			if n == 0 {
				clauses = append(clauses, clause)
				clause = nil
			} else {
				clause = append(clause, n)
			}
		}
	}
	if err := s.Err(); err != nil {
		return nil, err
	}
	if len(clause) > 0 {
		clauses = append(clauses, clause)
	}

	if problem.vars > 0 {
		vars := make(map[int]struct{})
		for _, clause := range clauses {
			for _, v := range clause {
				if v < 0 {
					v = -v
				}
				if v > problem.vars {
					return nil, fmt.Errorf("formula contains var %d, but problem line asserts %d vars (only vars in [1, %d] expected)",
						v, problem.vars, problem.vars)
				}
				vars[v] = struct{}{}
			}
		}
		// Allow some vars to be missing.
		if len(vars) > problem.vars {
			return nil, fmt.Errorf("problem line specifies %d vars, but there are %d", problem.vars, len(vars))
		}
		if len(clauses) != problem.clauses {
			return nil, fmt.Errorf("problem line specifies %d clauses, but there are %d", problem.clauses, len(clauses))
		}
	}
	return clauses, nil
}

// WriteDIMACS writes out the given problem in the DIMACS CNF format to w.
// It returns a non-nil error if the problem's variables don't form a contiguous
// set [1, n].
func WriteDIMACS(w io.Writer, problem [][]int) error {
	seen := make(map[int]struct{})
	var max int
	for _, cls := range problem {
		for _, v := range cls {
			if v == 0 {
				return errors.New("problem contains a 0 value")
			}
			if v < 0 {
				v = -v
			}
			seen[v] = struct{}{}
			if v > max {
				max = v
			}
		}
	}
	if max != len(seen) {
		return fmt.Errorf("problem has %d variables but largest var is %d (missing vars?)", len(seen), max)
	}
	bw := bufio.NewWriter(w)
	if _, err := fmt.Fprintf(bw, "p cnf %d %d\n", len(seen), len(problem)); err != nil {
		return err
	}
	for _, cls := range problem {
		for i, v := range cls {
			var s string
			if i > 0 {
				s = " "
			}
			if _, err := fmt.Fprintf(bw, "%s%d", s, v); err != nil {
				return err
			}
		}
		var s string
		if len(cls) > 0 {
			s = " "
		}
		if _, err := fmt.Fprintf(bw, "%s0\n", s); err != nil {
			return err
		}
	}
	return bw.Flush()
}
