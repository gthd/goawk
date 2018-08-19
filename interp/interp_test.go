// Tests for GoAWK interpreter.
package interp_test

import (
	"bytes"
	"flag"
	"fmt"
	"io/ioutil"
	"os"
	"os/exec"
	"strings"
	"testing"

	"github.com/benhoyt/goawk/interp"
	"github.com/benhoyt/goawk/parser"
)

var (
	awkExe string
)

func TestMain(m *testing.M) {
	flag.StringVar(&awkExe, "awk", "", "awk executable name")
	flag.Parse()
	os.Exit(m.Run())
}

// Note: a lot of these are really parser tests too.
func TestInterp(t *testing.T) {
	tests := []struct {
		src    string
		in     string
		out    string
		err    string
		awkErr string
	}{
		// BEGIN and END work correctly
		{`BEGIN { print "b" }`, "", "b\n", "", ""},
		{`BEGIN { print "b" }`, "foo", "b\n", "", ""},
		{`END { print "e" }`, "", "e\n", "", ""},
		{`END { print "e" }`, "foo", "e\n", "", ""},
		{`BEGIN { print "b"} END { print "e" }`, "", "b\ne\n", "", ""},
		{`BEGIN { print "b"} END { print "e" }`, "foo", "b\ne\n", "", ""},
		{`BEGIN { print "b"} $0 { print NR } END { print "e" }`, "foo", "b\n1\ne\n", "", ""},

		// Patterns
		{`$0`, "foo\n\nbar", "foo\nbar\n", "", ""},
		{`{ print $0 }`, "foo\n\nbar", "foo\n\nbar\n", "", ""},
		{`$1=="foo"`, "foo\n\nbar", "foo\n", "", ""},
		{`$1==42`, "foo\n42\nbar", "42\n", "", ""},
		{`$1=="42"`, "foo\n42\nbar", "42\n", "", ""},
		{`/foo/`, "foo\nx\nfood\nxfooz\nbar", "foo\nfood\nxfooz\n", "", ""},
		{`NR==2, NR==4`, "1\n2\n3\n4\n5\n6\n", "2\n3\n4\n", "", ""},
		{`
NR==2, NR==4 { print $0 }
NR==3, NR==5 { print NR }
`, "a\nb\nc\nd\ne\nf\ng", "b\nc\n3\nd\n4\n5\n", "", ""},

		// print and printf statements
		{`BEGIN { print "x", "y" }`, "", "x y\n", "", ""},
		{`BEGIN { OFS = ","; print "x", "y" }`, "", "x,y\n", "", ""},
		{`BEGIN { ORS = "."; print "x", "y" }`, "", "x y.", "", ""},
		{`BEGIN { ORS = ""; print "x", "y" }`, "", "x y", "", ""},
		{`{ print; print }`, "foo", "foo\nfoo\n", "", ""},
		{`BEGIN { print; print }`, "", "\n\n", "", ""},
		{`BEGIN { printf "%% %d %x %c %f %s", 42, 42, 42, 42, 42 }`, "", "% 42 2a * 42.000000 42", "", ""},
		{`BEGIN { printf "%3d", 42 }`, "", " 42", "", ""},
		{`BEGIN { printf "%3s", "x" }`, "", "  x", "", ""},
		{`BEGIN { printf "%.1g", 42 }`, "", "4e+01", "", ""},

		// if and loop statements
		{`BEGIN { if (1) print "t"; }`, "", "t\n", "", ""},
		{`BEGIN { if (0) print "t"; }`, "", "", "", ""},
		{`BEGIN { if (1) print "t"; else print "f" }`, "", "t\n", "", ""},
		{`BEGIN { if (0) print "t"; else print "f" }`, "", "f\n", "", ""},
		{`BEGIN { for (;;) { print "x"; break } }`, "", "x\n", "", ""},
		{`BEGIN { for (;;) { printf "%d ", i; i++; if (i>2) break; } }`, "", "0 1 2 ", "", ""},
		{`BEGIN { for (i=5; ; ) { printf "%d ", i; i++; if (i>8) break; } }`, "", "5 6 7 8 ", "", ""},
		{`BEGIN { for (i=5; ; i++) { printf "%d ", i; if (i>8) break; } }`, "", "5 6 7 8 9 ", "", ""},
		{`BEGIN { for (i=5; i<8; i++) { printf "%d ", i } }`, "", "5 6 7 ", "", ""},
		{`BEGIN { for (i=0; i<10; i++) { if (i < 5) continue; printf "%d ", i } }`, "", "5 6 7 8 9 ", "", ""},
		{`BEGIN { a["x"] = 3; a["y"] = 4; for (k in a) x += a[k]; print x }`, "", "7\n", "", ""},
		{`BEGIN { while (i < 5) { print i; i++ } }`, "", "\n1\n2\n3\n4\n", "", ""},
		{`BEGIN { do { print i; i++ } while (i < 5) }`, "", "\n1\n2\n3\n4\n", "", ""},

		// Arrays, "in", and delete
		{`BEGIN { a["x"] = 3; print "x" in a, "y" in a }`, "", "1 0\n", "", ""},
		{`BEGIN { a["x"] = 3; a["y"] = 4; delete a["x"]; for (k in a) print k, a[k] }`, "", "y 4\n", "", ""},
		{`BEGIN { a["x"] = 3; a["y"] = 4; for (k in a) delete a[k]; for (k in a) print k, a[k] }`, "", "", "", ""},

		// Unary expressions: ! + -
		{`BEGIN { print !42, !1, !0, !!42, !!1, !!0 }`, "", "0 0 1 1 1 0\n", "", ""},
		{`BEGIN { print !42, !1, !0, !!42, !!1, !!0 }`, "", "0 0 1 1 1 0\n", "", ""},
		{`BEGIN { print +4, +"3", +0, +-3, -3, - -4, -"3" }`, "", "4 3 0 -3 -3 4 -3\n", "", ""},

		// Binary expressions: == != < <= > >= + - * ^ / % CONCAT ~ !~
		{`BEGIN { print (1==1, 1==0, "1"==1, "1"==1.0) }`, "", "1 0 1 1\n", "", ""},
		// TODO: tests for numeric strings from $ fields

		// Other expressions: TODO ?: num str regex
		// Built-in variables: TODO
		// Field expressions and assignment: TODO
		// Assignment expressions: TODO
		// Incr/decr expressions: TODO

		// Builtin functions
		{`BEGIN { print sin(0), sin(0.5), sin(1), sin(-1) }`, "", "0 0.479426 0.841471 -0.841471\n", "", ""},
		{`BEGIN { print cos(0), cos(0.5), cos(1), cos(-1) }`, "", "1 0.877583 0.540302 0.540302\n", "", ""},
		{`BEGIN { print exp(0), exp(0.5), exp(1), exp(-1) }`, "", "1 1.64872 2.71828 0.367879\n", "", ""},
		{`BEGIN { print log(0), log(0.5), log(1), log(-1) }`, "", "-inf -0.693147 0 nan\n", "", ""},
		{`BEGIN { print sqrt(0), sqrt(2), sqrt(4), sqrt(-1) }`, "", "0 1.41421 2 nan\n", "", ""},
		{`BEGIN { print int(3.5), int("1.9"), int(4), int(-3.6), int("x"), int("") }`, "", "3 1 4 -3 0 0\n", "", ""},
		{`BEGIN { print match("food", "foo"), RSTART, RLENGTH }`, "", "1 1 3\n", "", ""},
		{`BEGIN { print match("x food y", "fo"), RSTART, RLENGTH }`, "", "3 3 2\n", "", ""},
		{`BEGIN { print match("x food y", "fox"), RSTART, RLENGTH }`, "", "0 0 -1\n", "", ""},
		{`BEGIN { print match("x food y", /[fod]+/), RSTART, RLENGTH }`, "", "3 3 4\n", "", ""},
		{`{ print length, length(), length("buzz"), length("") }`, "foo bar", "7 7 4 0\n", "", ""},
		{`BEGIN { print index("foo", "f"), index("foo0", 0), index("foo", "o"), index("foo", "x") }`, "", "1 4 2 0\n", "", ""},
		{`BEGIN { print atan2(1, 0.5), atan2(-1, 0) }`, "", "1.10715 -1.5708\n", "", ""},
		{`BEGIN { print sprintf("%3d", 42) }`, "", " 42\n", "", ""},
		{`BEGIN { print substr("food", 1) }`, "", "food\n", "", ""},
		{`BEGIN { print substr("food", 1, 2) }`, "", "fo\n", "", ""},
		{`BEGIN { print substr("food", 1, 4) }`, "", "food\n", "", ""},
		{`BEGIN { print substr("food", 1, 8) }`, "", "food\n", "", ""},
		{`BEGIN { print substr("food", 2) }`, "", "ood\n", "", ""},
		{`BEGIN { print substr("food", 2, 2) }`, "", "oo\n", "", ""},
		{`BEGIN { print substr("food", 2, 3) }`, "", "ood\n", "", ""},
		{`BEGIN { print substr("food", 2, 8) }`, "", "ood\n", "", ""},
		{`BEGIN { print substr("food", 0, 8) }`, "", "food\n", "", ""},
		{`BEGIN { print substr("food", -1, 8) }`, "", "food\n", "", ""},
		{`BEGIN { print substr("food", 5, 8) }`, "", "\n", "", ""},
		{`BEGIN { system("echo foo") }`, "", "foo\n", "", ""},
		{`BEGIN { n = split("ab c d ", a); for (i=1; i<=n; i++) print a[i] }`, "", "ab\nc\nd\n", "", ""},
		{`BEGIN { n = split("ab,c,d,", a, ","); for (i=1; i<=n; i++) print a[i] }`, "", "ab\nc\nd\n\n", "", ""},
		{`BEGIN { n = split("ab,c.d,", a, /[,.]/); for (i=1; i<=n; i++) print a[i] }`, "", "ab\nc\nd\n\n", "", ""},
		{`BEGIN { n = split("1 2", a); print (n, a[1], a[2], a[1]==1, a[2]==2) }`, "", "2 1 2 1 1\n", "", ""},
		{`BEGIN { x = "1.2.3"; print sub(/\./, ",", x); print x }`, "", "1\n1,2.3\n", "", ""},
		{`{ print sub(/\./, ","); print $0 }`, "1.2.3", "1\n1,2.3\n", "", ""},
		{`BEGIN { x = "1.2.3"; print gsub(/\./, ",", x); print x }`, "", "2\n1,2,3\n", "", ""},
		{`{ print gsub(/\./, ","); print $0 }`, "1.2.3", "2\n1,2,3\n", "", ""},
		{`{ print gsub(/[0-9]/, "(&)"); print $0 }`, "0123x. 42y", "6\n(0)(1)(2)(3)x. (4)(2)y\n", "", ""},
		{`{ print gsub(/[0-9]+/, "(&)"); print $0 }`, "0123x. 42y", "2\n(0123)x. (42)y\n", "", ""},
		{`{ print gsub(/[0-9]/, "\\&"); print $0 }`, "0123x. 42y", "6\n&&&&x. &&y\n", "", ""},
		{`BEGIN { print tolower("Foo BaR") }`, "", "foo bar\n", "", ""},
		{`BEGIN { print toupper("Foo BaR") }`, "", "FOO BAR\n", "", ""},
		{`
BEGIN {
	srand(1)
	a = rand(); b = rand(); c = rand()
	srand(1)
	x = rand(); y = rand(); z = rand()
	print (a==b, b==c, x==y, y==z)
	print (a==x, b==y, c==z)
}
`, "", "0 0 0 0\n1 1 1\n", "", ""},
		{`
BEGIN {
	for (i = 0; i < 1000; i++) {
		if (rand() < 0.5) n++
	}
	print (n>400)
}
`, "", "1\n", "", ""},

		// Conditional expressions parse and work correctly
		{`BEGIN { print 0?"t":"f" }`, "", "f\n", "", ""},
		{`BEGIN { print 1?"t":"f" }`, "", "t\n", "", ""},
		{`BEGIN { print (1+2)?"t":"f" }`, "", "t\n", "", ""},
		{`BEGIN { print (1+2?"t":"f") }`, "", "t\n", "", ""},
		{`BEGIN { print(1 ? x="t" : "f"); print x; }`, "", "t\nt\n", "", ""},

		// Locals vs globals, array params, and recursion
		{`
function f(loc) {
	glob += 1
	loc += 1
	print glob, loc
}
BEGIN {
	glob = 1
	loc = 42
	f(3)
	print loc
	f(4)
	print loc
}
`, "", "2 4\n42\n3 5\n42\n", "", ""},
		{`
function set(a, x, v) {
	a[x] = v
}
function get(a, x) {
	return a[x]
}
BEGIN {
	a["x"] = 1
	set(b, "y", 2)
	for (k in a) print k, a[k]
	print "---"
	for (k in b) print k, b[k]
	print "---"
	print get(a, "x"), get(b, "y")
}
`, "", "x 1\n---\ny 2\n---\n1 2\n", "", ""},
		{`
function fib(n) {
	return n < 3 ? 1 : fib(n-2) + fib(n-1)
}
BEGIN {
	for (i = 1; i <= 7; i++) {
		printf "%d ", fib(i)
	}
}
`, "", "1 1 2 3 5 8 13 ", "", ""},
		{`
function early() {
	print "x"
	return
	print "y"
}
BEGIN { early() }
`, "", "x\n", "", ""},

		// Greater than operator requires parentheses in print statement,
		// otherwise it's a redirection directive
		{`BEGIN { print "x" > "out" }`, "", "", "", ""},
		{`BEGIN { printf "x" > "out" }`, "", "", "", ""},
		{`BEGIN { print("x" > "out") }`, "", "1\n", "", ""},
		{`BEGIN { printf("x" > "out") }`, "", "1", "", ""},

		// Grammar should allow blocks wherever statements are allowed
		{`BEGIN { if (1) printf "x"; else printf "y" }`, "", "x", "", ""},
		// {`BEGIN { printf "x"; { printf "y"; printf "z" } }`, "", "xyz", "", ""},

		// Ensure certain odd syntax matches awk behaviour
		// {`BEGIN { printf "x" }; BEGIN { printf "y" }`, "", "xy", "", ""},
		// {`BEGIN { printf "x" };; BEGIN { printf "y" }`, "", "xy", "", ""},

		// Ensure syntax errors result in errors
		{`BEGIN { }'`, "", "", `parse error at 1:10: unexpected '\''`, "syntax error"},
		// {`{ $1 = substr($1, 1, 3) print $1 }`, "", "", "ERROR", "syntax error"},
	}
	for _, test := range tests {
		testName := test.src
		if len(testName) > 70 {
			testName = testName[:70]
		}

		if awkExe != "" {
			// Run it through external awk program first
			t.Run("awk_"+testName, func(t *testing.T) {
				srcFile, err := ioutil.TempFile("", "goawktest_")
				if err != nil {
					t.Fatalf("error creating temp file: %v", err)
				}
				defer os.Remove(srcFile.Name())
				_, err = srcFile.Write([]byte(test.src))
				if err != nil {
					t.Fatalf("error writing temp file: %v", err)
				}
				cmd := exec.Command(awkExe, "-f", srcFile.Name(), "-")
				if test.in != "" {
					stdin, err := cmd.StdinPipe()
					if err != nil {
						t.Fatalf("error fetching stdin pipe: %v", err)
					}
					go func() {
						defer stdin.Close()
						stdin.Write([]byte(test.in))
					}()
				}
				out, err := cmd.CombinedOutput()
				if err != nil {
					if test.awkErr != "" {
						if strings.Contains(string(out), test.awkErr) {
							return
						}
						t.Fatalf("expected error %q, got:\n%s", test.awkErr, out)
					} else {
						t.Fatalf("error running %s: %v:\n%s", awkExe, err, out)
					}
				}
				if test.awkErr != "" {
					t.Fatalf(`expected error %q, got ""`, test.awkErr)
				}
				if string(out) != test.out {
					t.Fatalf("expected %q, got %q", test.out, out)
				}
			})
		}

		// Then test it in GoAWK
		t.Run(testName, func(t *testing.T) {
			prog, err := parser.ParseProgram([]byte(test.src))
			if err != nil {
				if test.err != "" {
					if err.Error() == test.err {
						return
					}
					t.Fatalf("expected error %q, got %q", test.err, err.Error())
				}
				t.Fatal(err)
			}
			outBuf := &bytes.Buffer{}
			errBuf := &bytes.Buffer{}
			p := interp.New(outBuf, errBuf)
			err = p.Exec(prog, strings.NewReader(test.in), nil)
			if err != nil {
				if test.err != "" {
					if err.Error() == test.err {
						return
					}
					t.Fatalf("expected error %q, got %q", test.err, err.Error())
				}
				t.Fatal(err)
			}
			if test.err != "" {
				t.Fatalf(`expected error %q, got ""`, test.err)
			}
			out := outBuf.String() + errBuf.String()
			if out != test.out {
				t.Fatalf("expected %q, got %q", test.out, out)
			}
		})
	}
	_ = os.Remove("out")
}

func benchmarkProgram(b *testing.B, n int, input, expected, srcFormat string, args ...interface{}) {
	b.StopTimer()
	src := fmt.Sprintf(srcFormat, args...)
	prog, err := parser.ParseProgram([]byte(src))
	if err != nil {
		b.Fatalf("error parsing %s: %v", b.Name(), err)
	}
	outBuf := &bytes.Buffer{}
	p := interp.New(outBuf, ioutil.Discard)
	if expected != "" {
		expected += "\n"
	}
	for i := 0; i < n; i++ {
		outBuf.Reset()
		b.StartTimer()
		err := p.Exec(prog, strings.NewReader(input), nil)
		b.StopTimer()
		if err != nil {
			b.Fatalf("error interpreting %s: %v", b.Name(), err)
		}
		if outBuf.String() != expected {
			b.Fatalf("expected %q, got %q", expected, outBuf.String())
		}
	}
}

func BenchmarkRecursiveFunc(b *testing.B) {
	benchmarkProgram(b, b.N, "", "13", `
function fib(n) {
  if (n <= 2) {
    return 1
  }
  return fib(n-1) + fib(n-2)
}

BEGIN {
  print fib(7)
}
`)
}

func BenchmarkFuncCall(b *testing.B) {
	b.StopTimer()
	sum := 0
	for i := 0; i < b.N; i++ {
		sum += i
	}
	benchmarkProgram(b, 1, "", fmt.Sprintf("%d", sum), `
function add(a, b) {
  return a + b
}

BEGIN {
  for (i = 0; i < %d; i++) {
    sum = add(sum, i)
  }
  print sum
}
`, b.N)
}

func BenchmarkForLoop(b *testing.B) {
	b.StopTimer()
	sum := 0
	for i := 0; i < b.N; i++ {
		sum += i
	}
	benchmarkProgram(b, 1, "", fmt.Sprintf("%d", sum), `
BEGIN {
  for (i = 0; i < %d; i++) {
    sum += i
  }
  print sum
}
`, b.N)
}

func BenchmarkSimplePattern(b *testing.B) {
	b.StopTimer()
	inputLines := []string{}
	expectedLines := []string{}
	for i := 0; i < b.N; i++ {
		if i != 0 && i%2 == 0 {
			line := fmt.Sprintf("%d", i)
			inputLines = append(inputLines, line)
			expectedLines = append(expectedLines, line)
		} else {
			inputLines = append(inputLines, "")
		}
	}
	input := strings.Join(inputLines, "\n")
	expected := strings.Join(expectedLines, "\n")
	benchmarkProgram(b, 1, input, expected, "$0")
}

func BenchmarkFields(b *testing.B) {
	b.StopTimer()
	inputLines := []string{}
	expectedLines := []string{}
	for i := 1; i < b.N+1; i++ {
		inputLines = append(inputLines, fmt.Sprintf("%d %d %d", i, i*2, i*3))
		expectedLines = append(expectedLines, fmt.Sprintf("%d %d", i, i*3))
	}
	input := strings.Join(inputLines, "\n")
	expected := strings.Join(expectedLines, "\n")
	benchmarkProgram(b, 1, input, expected, "{ print $1, $3 }")
}

func Example_simple() {
	input := bytes.NewReader([]byte("foo bar\n\nbaz buz"))
	err := interp.Exec("$0 { print $1 }", " ", input, nil)
	if err != nil {
		fmt.Println(err)
		return
	}
	// Output:
	// foo
	// baz
}

func Example_program() {
	src := "{ print $1+$2 }"
	input := "1,2\n3,4\n5,6"

	prog, err := parser.ParseProgram([]byte(src))
	if err != nil {
		fmt.Println(err)
		return
	}
	p := interp.New(nil, nil)
	p.SetVar("FS", ",")
	err = p.Exec(prog, bytes.NewReader([]byte(input)), nil)
	if err != nil {
		fmt.Println(err)
		return
	}
	// Output:
	// 3
	// 7
	// 11
}

func Example_expression() {
	src := "1 + 2 * 3 / 4"

	expr, err := parser.ParseExpr([]byte(src))
	if err != nil {
		fmt.Println(err)
		return
	}
	p := interp.New(nil, nil)
	n, err := p.EvalNum(expr)
	if err != nil {
		fmt.Println(err)
		return
	}
	fmt.Println(n)
	// Output:
	// 2.5
}
