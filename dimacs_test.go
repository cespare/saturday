package saturday

import (
	"fmt"
	"strings"
	"testing"

	"github.com/google/go-cmp/cmp"
	"github.com/google/go-cmp/cmp/cmpopts"
)

func TestParseDIMACS(t *testing.T) {
	for _, tt := range []struct {
		text      string
		want      [][]int
		roundtrip string // if different from text with the comments removed
	}{
		{
			text: `
c No vars or clauses
p cnf 0 0
`,
			want: [][]int{},
		},
		{
			text: `
c No clauses
p cnf 5 0
`,
			want: [][]int{},
			roundtrip: `
p cnf 0 0
`,
		},
		{
			text: `
c 1 var, 1 clause
p cnf 1 1
1 0
`,
			want: [][]int{{1}},
		},
		{
			text: `
c Empty clauses
p cnf 3 5
1 3 0 0 -3 0
0 -2 -1
`,
			want: [][]int{{1, 3}, {}, {-3}, {}, {-2, -1}},
			roundtrip: `
p cnf 3 5
1 3 0
0
-3 0
0
-2 -1 0
`,
		},
		{
			text: `
c DIMACS example file
c
p cnf 4 3
1 3 -4 0
4 0 2
-3
`,
			want: [][]int{{1, 3, -4}, {4}, {2, -3}},
			roundtrip: `
p cnf 4 3
1 3 -4 0
4 0
2 -3 0
`,
		},
		{
			text: `
c percent sign
p cnf 2 2
1 2 0
-1 2 0
%
1 2 3
x y z
`,
			want: [][]int{{1, 2}, {-1, 2}},
			roundtrip: `
p cnf 2 2
1 2 0
-1 2 0
`,
		},
	} {
		text := strings.TrimSpace(tt.text)
		roundtrip := tt.roundtrip
		if roundtrip == "" {
			var b strings.Builder
			for _, line := range strings.Split(text, "\n") {
				if !strings.HasPrefix(line, "c") {
					fmt.Fprintln(&b, line)
				}
			}
			roundtrip = b.String()
		}
		roundtrip = strings.TrimSpace(roundtrip)
		name := strings.TrimPrefix(text[:strings.IndexByte(text, '\n')], "c ")
		t.Run(name, func(t *testing.T) {
			got, err := ParseDIMACS(strings.NewReader(text))
			if err != nil {
				t.Fatal(err)
			}
			if diff := cmp.Diff(got, tt.want, cmpopts.EquateEmpty()); diff != "" {
				t.Fatalf("ParseDIMACS (-got, +want):\n%s", diff)
			}

			var b strings.Builder
			if err := WriteDIMACS(&b, tt.want); err != nil {
				t.Fatal(err)
			}
			gotText := strings.TrimSpace(b.String())
			if gotText != roundtrip {
				t.Fatalf("WriteDIMACS(%v): got\n\n%s\n\nwant:\n\n%s\n\n", tt.want, gotText, roundtrip)
			}
		})
	}
}

func TestParseDIMACSPercent(t *testing.T) {
	in := `p cnf 2 2
1 2 0
-1 2 0
%
1 2 3
x y z
`
	got, err := ParseDIMACS(strings.NewReader(in))
	if err != nil {
		t.Fatal(err)
	}
	want := [][]int{{1, 2}, {-1, 2}}
	if diff := cmp.Diff(got, want, cmpopts.EquateEmpty()); diff != "" {
		t.Fatalf("ParseDIMACS (-got, +want):\n%s", diff)
	}
}
