package saturday

import (
	"strings"
	"testing"

	"github.com/google/go-cmp/cmp"
	"github.com/google/go-cmp/cmp/cmpopts"
)

func TestParseDIMACS(t *testing.T) {
	for _, tt := range []struct {
		text string
		want [][]int
	}{
		{
			text: `
c Trivial
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
		},
	} {
		text := strings.TrimSpace(tt.text)
		name := strings.TrimPrefix(text[:strings.IndexByte(text, '\n')], "c ")
		t.Run(name, func(t *testing.T) {
			got, err := ParseDIMACS(strings.NewReader(text))
			if err != nil {
				t.Fatal(err)
			}
			if diff := cmp.Diff(got, tt.want, cmpopts.EquateEmpty()); diff != "" {
				t.Fatalf("ParseDIMACS (-got, +want):\n%s", diff)
			}
		})
	}
}
