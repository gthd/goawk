// Package interp is the GoAWK interpreter (a simple tree-walker).
//
// For basic usage, use the Exec function. For more complicated use
// cases and configuration options, first use the parser package to
// parse the AWK source, and then use ExecProgram to execute it with
// a specific configuration.
//
package interp

import (
	"bufio"
	"errors"
	"fmt"
	"io"
	"io/ioutil"
	"math"
	"math/rand"
	"os"
	"os/exec"
	"regexp"
	"runtime"
	// "reflect"
	"strconv"
	"strings"
	"unicode/utf8"

	. "github.com/gthd/goawk/internal/ast"
	. "github.com/gthd/goawk/lexer"
	. "github.com/gthd/goawk/parser"
)

var (
	errExit     = errors.New("exit")
	errBreak    = errors.New("break")
	errContinue = errors.New("continue")
	errNext     = errors.New("next")

	crlfNewline = runtime.GOOS == "windows"
	varRegex    = regexp.MustCompile(`^([_a-zA-Z][_a-zA-Z0-9]*)=(.*)`)
	myValues map[string]value
)

// Error (actually *Error) is returned by Exec and Eval functions on
// interpreter error, for example a negative field index.
type Error struct {
	message string
}

func (e *Error) Error() string {
	return e.message
}

func newError(format string, args ...interface{}) error {
	return &Error{fmt.Sprintf(format, args...)}
}

type returnValue struct {
	Value value
}

func (r returnValue) Error() string {
	return "<return " + r.Value.str("%.6g") + ">"
}

type interp struct {
	// Input/output
	output        io.Writer
	flushOutput   bool
	errorOutput   io.Writer
	flushError    bool
	scanner       *bufio.Scanner
	scanners      map[string]*bufio.Scanner
	stdin         io.Reader
	filenameIndex int
	hadFiles      bool
	input         io.Reader
	inputStreams  map[string]io.ReadCloser
	outputStreams map[string]io.WriteCloser
	commands      map[string]*exec.Cmd
	noExec        bool
	noFileWrites  bool
	noFileReads   bool

	// Scalars, arrays, and function state
	globals     []value
	stack       []value
	frame       []value
	arrays      []map[string]value
	localArrays [][]int
	callDepth   int
	nativeFuncs []nativeFunc
	offset int64

	// File, line, and field handling
	filename    string
	line        string
	lineNum     int
	fileLineNum int
	fields      []string
	numFields   int
	haveFields  bool

	// Built-in variables
	argc            int
	convertFormat   string
	outputFormat    string
	fieldSep        string
	fieldSepRegex   *regexp.Regexp
	recordSep       string
	outputFieldSep  string
	outputRecordSep string
	subscriptSep    string
	matchLength     int
	matchStart      int

	// Misc pieces of state
	program     *Program
	random      *rand.Rand
	randSeed    float64
	exitStatus  int
	regexCache  map[string]*regexp.Regexp
	formatCache map[string]cachedFormat
}

// Various const configuration. Could make these part of Config if
// we wanted to, but no need for now.
const (
	maxCachedRegexes = 100
	maxCachedFormats = 100
	maxRecordLength  = 10 * 1024 * 1024 // 10MB seems like plenty
	maxFieldIndex    = 1000000
	maxCallDepth     = 1000
	initialStackSize = 100
	outputBufSize    = 64 * 1024
	stderrBufSize    = 4 * 1024
	inputBufSize     = 64 * 1024
)

// Config defines the interpreter configuration for ExecProgram.
type Config struct {
	// Standard input reader (defaults to os.Stdin)
	Stdin io.Reader

	// Writer for normal output (defaults to a buffered version of
	// os.Stdout)
	Output io.Writer

	// Writer for non-fatal error messages (defaults to a buffered
	// version of os.Stderr)
	Error io.Writer

	// The name of the executable (accessible via ARGV[0])
	Argv0 string

	// Input arguments (usually filenames): empty slice means read
	// only from Stdin, and a filename of "-" means read from Stdin
	// instead of a real file.
	Args []string

	// List of name-value pairs for variables to set before executing
	// the program (useful for setting FS and other built-in
	// variables, for example []string{"FS", ",", "OFS", ","}).
	Vars []string

	// Map of named Go functions to allow calling from AWK. You need
	// to pass this same map to the parser.ParseProgram config.
	//
	// Functions can have any number of parameters, and variadic
	// functions are supported. Functions can have no return values,
	// one return value, or two return values (result, error). In the
	// two-value case, if the function returns a non-nil error,
	// program execution will stop and ExecProgram will return that
	// error.
	//
	// Apart from the error return value, the types supported are
	// bool, integer and floating point types (excluding complex),
	// and string types (string or []byte).
	//
	// It's not an error to call a Go function from AWK with fewer
	// arguments than it has parameters in Go. In this case, the zero
	// value will be used for any additional parameters. However, it
	// is a parse error to call a non-variadic function from AWK with
	// more arguments than it has parameters in Go.
	//
	// Functions defined with the "function" keyword in AWK code
	// take precedence over functions in Funcs.
	Funcs map[string]interface{}

	// Set one or more of these to true to prevent unsafe behaviours,
	// useful when executing untrusted scripts:
	//
	// * NoExec prevents system calls via system() or pipe operator
	// * NoFileWrites prevents writing to files via '>' or '>>'
	// * NoFileReads prevents reading from files via getline or the
	//   filenames in Args
	NoExec       bool
	NoFileWrites bool
	NoFileReads  bool
	Offset int64
}

// ExecProgram executes the parsed program using the given interpreter
// config, returning the exit status code of the program. Error is nil
// on successful execution of the program, even if the program returns
// a non-zero status code.
func ExecProgram(program *Program, config *Config) (int, error, []float64, []bool, []string, map[string]float64) {
	var res []float64
	var natives []bool
	var names []string
	var myArrays map[string]float64
	if len(config.Vars)%2 != 0 {
		return 0, newError("length of config.Vars must be a multiple of 2, not %d", len(config.Vars)), res, natives, names, myArrays
	}

	p := &interp{program: program}

	// Allocate memory for variables
	p.globals = make([]value, len(program.Scalars))
	p.stack = make([]value, 0, initialStackSize)
	p.arrays = make([]map[string]value, len(program.Arrays), len(program.Arrays)+initialStackSize)
	for i := 0; i < len(program.Arrays); i++ {
		p.arrays[i] = make(map[string]value)
	}

	// Initialize defaults
	p.regexCache = make(map[string]*regexp.Regexp, 10)
	p.formatCache = make(map[string]cachedFormat, 10)
	p.randSeed = 1.0
	seed := math.Float64bits(p.randSeed)
	p.random = rand.New(rand.NewSource(int64(seed)))
	p.convertFormat = "%.6g"
	p.outputFormat = "%.6g"
	p.fieldSep = " "
	p.recordSep = "\n"
	p.outputFieldSep = " "
	p.outputRecordSep = "\n"
	p.subscriptSep = "\x1c"
	p.noExec = config.NoExec
	p.noFileWrites = config.NoFileWrites
	p.noFileReads = config.NoFileReads
	p.offset = config.Offset
	err := p.initNativeFuncs(config.Funcs)
	if err != nil {
		return 0, err, res, natives, names, myArrays
	}

	names = make([]string, 0, len(config.Funcs))
	for k := range config.Funcs {
		names = append(names, k)
	}

	// Setup ARGV and other variables from config
	argvIndex := program.Arrays["ARGV"]
	p.setArrayValue(ScopeGlobal, argvIndex, "0", str(config.Argv0))
	p.argc = len(config.Args) + 1
	for i, arg := range config.Args {
		p.setArrayValue(ScopeGlobal, argvIndex, strconv.Itoa(i+1), str(arg))
	}
	p.filenameIndex = 1
	p.hadFiles = false
	for i := 0; i < len(config.Vars); i += 2 {
		err := p.setVarByName(config.Vars[i], config.Vars[i+1])
		if err != nil {
			return 0, err, res, natives, names, myArrays
		}
	}

	// Setup I/O structures
	p.stdin = config.Stdin
	if p.stdin == nil {
		p.stdin = os.Stdin
	}
	p.output = config.Output
	if p.output == nil {
		p.output = bufio.NewWriterSize(os.Stdout, outputBufSize)
		p.flushOutput = true
	}
	p.errorOutput = config.Error
	if p.errorOutput == nil {
		p.errorOutput = bufio.NewWriterSize(os.Stderr, stderrBufSize)
		p.flushError = true
	}
	p.inputStreams = make(map[string]io.ReadCloser)
	p.outputStreams = make(map[string]io.WriteCloser)
	p.commands = make(map[string]*exec.Cmd)
	p.scanners = make(map[string]*bufio.Scanner)
	defer p.closeAll()

	// Execute the program! BEGIN, then pattern/actions, then END
	err = p.execBeginEnd(program.Begin)
	if err != nil && err != errExit {
		return 0, err, res, natives, names, myArrays
	}
	if program.Actions == nil && program.End == nil {
		return p.exitStatus, nil, res, natives, names, myArrays
	}
	if err != errExit {
		err, res, natives, myArrays = p.execActions(program.Actions)
		if err != nil && err != errExit {
			return 0, err, res, natives, names, myArrays
		}
	}
	return p.exitStatus, nil, res, natives, names, myArrays
}

func ExecOneThread(program *Program, config *Config, associativeArrays map[int]map[string]float64) (int, error, []float64) {
	var res []float64
	// myValues := make(map[string]*value)
	if len(config.Vars)%2 != 0 {
		return 0, newError("length of config.Vars must be a multiple of 2, not %d", len(config.Vars)), res
	}

	p := &interp{program: program}

	// Allocate memory for variables
	p.globals = make([]value, len(program.Scalars))
	p.stack = make([]value, 0, initialStackSize)
	p.arrays = make([]map[string]value, len(program.Arrays), len(program.Arrays)+initialStackSize)
	for i := 0; i < len(program.Arrays); i++ {
		myValues := make(map[string]value)
		if len(associativeArrays[i]) > 0 {
			keys := make([]string, 0, len(associativeArrays[i]))
			for k := range associativeArrays[i] {
				keys = append(keys, k)
			}
			for _, k := range keys {
				myValues[k] = value{2, "", associativeArrays[i][k]}
			}
			p.arrays[i] = myValues
		} else {
			p.arrays[i] = make(map[string]value)
		}
	}

	// Initialize defaults
	p.regexCache = make(map[string]*regexp.Regexp, 10)
	p.formatCache = make(map[string]cachedFormat, 10)
	p.randSeed = 1.0
	seed := math.Float64bits(p.randSeed)
	p.random = rand.New(rand.NewSource(int64(seed)))
	p.convertFormat = "%.6g"
	p.outputFormat = "%.6g"
	p.fieldSep = " "
	p.recordSep = "\n"
	p.outputFieldSep = " "
	p.outputRecordSep = "\n"
	p.subscriptSep = "\x1c"
	p.noExec = config.NoExec
	p.noFileWrites = config.NoFileWrites
	p.noFileReads = config.NoFileReads
	err := p.initNativeFuncs(config.Funcs)
	if err != nil {
		return 0, err, res
	}

	// Setup ARGV and other variables from config
	argvIndex := program.Arrays["ARGV"]
	p.setArrayValue(ScopeGlobal, argvIndex, "0", str(config.Argv0))
	p.argc = len(config.Args) + 1
	for i, arg := range config.Args {
		p.setArrayValue(ScopeGlobal, argvIndex, strconv.Itoa(i+1), str(arg))
	}
	p.filenameIndex = 1
	p.hadFiles = false
	for i := 0; i < len(config.Vars); i += 2 {
		err := p.setVarByName(config.Vars[i], config.Vars[i+1])
		if err != nil {
			return 0, err, res
		}
	}

	variable_names := make([]string, 0, len(p.program.Scalars))
	for k := range p.program.Scalars {
		variable_names = append(variable_names, k)
	}

	for iter, name := range variable_names {
		s := fmt.Sprintf("%f", p.program.Scalars[name])
		err := p.setVar(ScopeGlobal, iter, numStr(s))
		if err != nil {
			return 0, err, res
		}
	}

	// Setup I/O structures
	p.stdin = config.Stdin
	if p.stdin == nil {
		p.stdin = os.Stdin
	}
	p.output = config.Output
	if p.output == nil {
		p.output = bufio.NewWriterSize(os.Stdout, outputBufSize)
		p.flushOutput = true
	}
	p.errorOutput = config.Error
	if p.errorOutput == nil {
		p.errorOutput = bufio.NewWriterSize(os.Stderr, stderrBufSize)
		p.flushError = true
	}
	p.inputStreams = make(map[string]io.ReadCloser)
	p.outputStreams = make(map[string]io.WriteCloser)
	p.commands = make(map[string]*exec.Cmd)
	p.scanners = make(map[string]*bufio.Scanner)
	defer p.closeAll()

	if program.Actions == nil && program.End == nil {
		return p.exitStatus, nil, res
	}
	if err != errExit {
		err, res, _, _ = p.execActions(program.Actions)
		if err != nil && err != errExit {
			return 0, err, res
		}
	}

	err = p.execBeginEnd(program.End)
	if err != nil && err != errExit {
		return 0, err, res
	}
	return p.exitStatus, nil, res
}

// Exec provides a simple way to parse and execute an AWK program
// with the given field separator. Exec reads input from the given
// reader (nil means use os.Stdin) and writes output to stdout (nil
// means use a buffered version of os.Stdout).
func Exec(source, fieldSep string, input io.Reader, output io.Writer) error {
	prog, err, _ := ParseProgram([]byte(source), nil)
	if err != nil {
		return err
	}
	config := &Config{
		Stdin:  input,
		Output: output,
		Error:  ioutil.Discard,
		Vars:   []string{"FS", fieldSep},
	}
	_, err, _, _, _, _= ExecProgram(prog, config)
	return err
}

// Execute BEGIN or END blocks (may be multiple)
func (p *interp) execBeginEnd(beginEnd []Stmts) error {
	for _, statements := range beginEnd {
		err, _, _, _ := p.executes(statements)
		if err != nil {
			return err
		}
	}
	return nil
}

// Execute pattern-action blocks (may be multiple)
func (p *interp) execActions(actions []Action) (error, []float64, []bool, map[string]float64) {
	inRange := make([]bool, len(actions))
	var myBArrays []map[int64]string
	var res []float64
	var natives []bool
	var newArray map[string]float64
	newArray = make(map[string]float64)
lineLoop:
	for {
		// Read and setup next line of input
		line, err := p.nextLine()
		if err == io.EOF {
			break
		}
		if err != nil {
			return err, res, natives, newArray
		}
		p.setLine(line)
		// Execute all the pattern-action blocks for each line
		for i, action := range actions {
			// First determine whether the pattern matches
			matched := false
			switch len(action.Pattern) {
			case 0:
				// No pattern is equivalent to pattern evaluating to true
				matched = true
			case 1:
				// Single boolean pattern
				v, _, err, _ := p.eval(action.Pattern[0])
				if err != nil {
					return err, res, natives, newArray
				}
				matched = v.boolean()
			case 2:
				// Range pattern (matches between start and stop lines)
				if !inRange[i] {
					v, _, err, _ := p.eval(action.Pattern[0])
					if err != nil {
						return err, res, natives, newArray
					}
					inRange[i] = v.boolean()
				}
				matched = inRange[i]
				if inRange[i] {
					v, _, err, _ := p.eval(action.Pattern[1])
					if err != nil {
						return err, res, natives, newArray
					}
					inRange[i] = !v.boolean()
				}
			}
			if !matched {
				continue
			}

			// No action is equivalent to { print $0 }
			if action.Stmts == nil {
				err := p.printLine(p.output, p.line)
				if err != nil {
					return err, res, natives, newArray
				}
				continue
			}

			// Execute the body statements
			err, res, natives, myBArrays = p.executes(action.Stmts)

			if len(myBArrays) > 0 {
				for key, value := range myBArrays[0] {
					newArray[value] = float64(key)
				}
			}

			if err == errNext {
				// "next" statement skips straight to next line
				continue lineLoop
			}
			if err != nil {
				return err, res, natives, newArray
			}
		}
	}
	return nil, res, natives, newArray
}

func (p *interp) executes(stmts Stmts) (error, []float64, []bool, []map[int64]string) {
	var results []float64
	var natives []bool
	var myArrays []map[int64]string
	for _, s := range stmts {
		nativeFunction = false
		err, res, nativeFunction, myArray := p.execute(s)
		if err != nil {
			return err, results, natives, myArrays
		}
		results = append(results, res)
		natives = append(natives, nativeFunction)
		myArrays = append(myArrays, myArray)
	}

	return nil, results, natives, myArrays
}

// Execute a single statement
func (p *interp) execute(stmt Stmt) (error, float64, bool, map[int64]string) {
	var myArray map[int64]string
	switch s := stmt.(type) {
	case *ExprStmt:
		// Expression statement: simply throw away the expression value		
		res, nativeFunction, err, myArray := p.eval(s.Expr)
		return err, res.n, nativeFunction, myArray

	case *PrintStmt:
		// Print OFS-separated args followed by ORS (usually newline)
		var line string
		if len(s.Args) > 0 {
			strs := make([]string, len(s.Args))
			for i, a := range s.Args {
				v, nativeFunction, err, myArray := p.eval(a)
				if err != nil {
					return err, 0, nativeFunction, myArray
				}
				strs[i] = v.str(p.outputFormat)
			}
			line = strings.Join(strs, p.outputFieldSep)
		} else {
			// "print" with no args is equivalent to "print $0"
			line = p.line
		}
		output, err := p.getOutputStream(s.Redirect, s.Dest)
		if err != nil {
			return err, 0, nativeFunction, myArray
		}
		return p.printLine(output, line), 0, nativeFunction, myArray

	case *PrintfStmt:
		// printf(fmt, arg1, arg2, ...): uses our version of sprintf
		// to build the formatted string and then print that
		formatValue, nativeFunction, err, myArray := p.eval(s.Args[0])
		if err != nil {
			return err, 0, nativeFunction, myArray
		}
		format := p.toString(formatValue)
		args := make([]value, len(s.Args)-1)
		for i, a := range s.Args[1:] {
			args[i], nativeFunction, err, myArray = p.eval(a)
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
		}
		output, err := p.getOutputStream(s.Redirect, s.Dest)
		if err != nil {
			return err, 0, nativeFunction, myArray
		}
		str, err := p.sprintf(format, args)
		if err != nil {
			return err, 0, nativeFunction, myArray
		}
		err = writeOutput(output, str)
		if err != nil {
			return err, 0, nativeFunction, myArray
		}

	case *IfStmt: //see what it has to return in order to add up correctly
		v, nativeFunction, err, myArray := p.eval(s.Cond)
		if err != nil {
			return err, 0, nativeFunction, myArray
		}
		if v.boolean() {
			err, _, _, _ := p.executes(s.Body)
			return err, 0, nativeFunction, myArray
		} else {
			// Doesn't do anything if s.Else is nil
			err, _, _, _ := p.executes(s.Else)
			return err, 0, nativeFunction, myArray
		}

	case *ForStmt:
		// C-like for loop with pre-statement, cond, and post-statement
		if s.Pre != nil {
			err, _, _, _ := p.execute(s.Pre)
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
		}
		for {
			if s.Cond != nil {
				v, nativeFunction, err, myArray := p.eval(s.Cond)
				if err != nil {
					return err, 0, nativeFunction, myArray
				}
				if !v.boolean() {
					break
				}
			}
			err, _, _, _ := p.executes(s.Body)
			if err == errBreak {
				break
			}
			if err != nil && err != errContinue {
				return err, 0, nativeFunction, myArray
			}
			if s.Post != nil {
				err, _, _, _ := p.execute(s.Post)
				if err != nil {
					return err, 0, nativeFunction, myArray
				}
			}
		}

	case *ForInStmt:
		// Foreach-style "for (key in array)" loop
		array := p.arrays[p.getArrayIndex(s.Array.Scope, s.Array.Index)]
		for index := range array {
			err := p.setVar(s.Var.Scope, s.Var.Index, str(index))
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
			err, _, _, _ = p.executes(s.Body)
			if err == errBreak {
				break
			}
			if err == errContinue {
				continue
			}
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
		}

	case *ReturnStmt:
		// Return statement uses special error value which is "caught"
		// by the callUser function
		var v value
		if s.Value != nil {
			var err error
			v, nativeFunction, err, myArray = p.eval(s.Value)
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
		}
		return returnValue{v}, 0, nativeFunction, myArray

	case *WhileStmt:
		// Simple "while (cond)" loop
		for {
			v, nativeFunction, err, myArray := p.eval(s.Cond)
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
			if !v.boolean() {
				break
			}
			err, _, _, _ = p.executes(s.Body)
			if err == errBreak {
				break
			}
			if err == errContinue {
				continue
			}
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
		}

	case *DoWhileStmt:
		// Do-while loop (tests condition after executing body)
		for {
			err, _, _, _ := p.executes(s.Body)
			if err == errBreak {
				break
			}
			if err == errContinue {
				continue
			}
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
			v, nativeFunction, err, myArray := p.eval(s.Cond)
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
			if !v.boolean() {
				break
			}
		}

	// Break, continue, next, and exit statements
	case *BreakStmt:
		return errBreak, 0, nativeFunction, myArray
	case *ContinueStmt:
		return errContinue, 0, nativeFunction, myArray
	case *NextStmt:
		return errNext, 0, nativeFunction, myArray
	case *ExitStmt:
		if s.Status != nil {
			status, nativeFunction, err, myArray := p.eval(s.Status)
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
			p.exitStatus = int(status.num())
		}
		// Return special errExit value "caught" by top-level executor
		return errExit, 0, nativeFunction, myArray

	case *DeleteStmt:
		if len(s.Index) > 0 {
			// Delete single key from array
			index, err := p.evalIndex(s.Index)
			if err != nil {
				return err, 0, nativeFunction, myArray
			}
			array := p.arrays[p.getArrayIndex(s.Array.Scope, s.Array.Index)]
			delete(array, index) // Does nothing if key isn't present
		} else {
			// Delete entire array
			array := p.arrays[p.getArrayIndex(s.Array.Scope, s.Array.Index)]
			for k := range array {
				delete(array, k)
			}
		}

	// case *BlockStmt:
	// 	// Nested block (just syntax, doesn't do anything)
	// 	return p.executes(s.Body), 0

	default:
		// Should never happen
		panic(fmt.Sprintf("unexpected stmt type: %T", stmt))
	}
	return nil, 0, nativeFunction, myArray
}

var nativeFunction bool
// Evaluate a single expression, return expression value and error
func (p *interp) eval(expr Expr) (value, bool, error, map[int64]string) {
	var myOptimisedArray map[int64]string
	switch e := expr.(type) {
	case *NumExpr:
		// Number literal
		return num(e.Value), nativeFunction, nil, myOptimisedArray

	case *StrExpr:
		// String literal
		return str(e.Value), nativeFunction, nil, myOptimisedArray

	case *FieldExpr: //returns what is needed
		// $n field expression
		index, nativeFunction, err, _ := p.eval(e.Index)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		getfield, err := p.getField(int(index.num()))
		return getfield, nativeFunction, err, myOptimisedArray

	case *VarExpr:
		// Variable read expression (scope is global, local, or special)
		return p.getVar(e.Scope, e.Index), nativeFunction, nil, myOptimisedArray

	case *RegExpr:
		// Stand-alone /regex/ is equivalent to: $0 ~ /regex/
		re, err := p.compileRegex(e.Regex)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		return boolean(re.MatchString(p.line)), nativeFunction, nil, myOptimisedArray

	case *BinaryExpr:
		// Binary expression. Note that && and || are special cases
		// as they're short-circuit operators.
		// if e.Left.String() == "NR" {
		// 	fmt.Println(e.Right.String())
		// }
		left, _, err, _ := p.eval(e.Left)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		switch e.Op {
		case AND:
			if !left.boolean() {
				return num(0), nativeFunction, nil, myOptimisedArray
			}
			right, _, err, _ := p.eval(e.Right)
			if err != nil {
				return null(), nativeFunction, err, myOptimisedArray
			}
			return boolean(right.boolean()), nativeFunction, nil, myOptimisedArray
		case OR:
			if left.boolean() {
				return num(1), nativeFunction, nil, myOptimisedArray
			}
			right, _, err, _ := p.eval(e.Right)
			if err != nil {
				return null(), nativeFunction, err, myOptimisedArray
			}
			return boolean(right.boolean()), nativeFunction, nil, myOptimisedArray
		default:
			right, _, err, _ := p.eval(e.Right)
			if err != nil {
				return null(), nativeFunction, err, myOptimisedArray
			}
			evalbinary, err := p.evalBinary(e.Op, left, right)
			return evalbinary, nativeFunction, err, myOptimisedArray
		}

	case *IncrExpr:
		// Pre-increment, post-increment, pre-decrement, post-decrement

		// First evaluate the expression, but remember array or field
		// index so we don't evaluate part of the expression twice
		exprValue, arrayIndex, fieldIndex, err := p.evalForAugAssign(e.Expr)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}

		// Then convert to number and increment or decrement
		exprNum := exprValue.num()
		var incr float64
		if e.Op == INCR {
			incr = exprNum + 1
		} else {
			incr = exprNum - 1
		}
		incrValue := num(incr)

		// Finally assign back to expression and return the correct value
		err = p.assignAug(e.Expr, arrayIndex, fieldIndex, incrValue)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		if e.Pre {
			return incrValue, nativeFunction, nil, myOptimisedArray
		} else {
			return num(exprNum), nativeFunction, nil, myOptimisedArray
		}

	case *AssignExpr:
		// Assignment expression (returns right-hand side)
		right, _, err, _ := p.eval(e.Right)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		err = p.assign(e.Left, right)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		return right, nativeFunction, nil, myOptimisedArray

	case *AugAssignExpr:
		// Augmented assignment like += (returns right-hand side)
		right, _, err, _ := p.eval(e.Right)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		left, arrayIndex, fieldIndex, err := p.evalForAugAssign(e.Left)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		// if e.Op.String() == "+" {
		// 	myArray[arrayIndex] = right.n + left.n
		// } else if e.Op.String() == "-" {
		// 	myArray[arrayIndex] = right.n - left.n
		// }

		right, err = p.evalBinary(e.Op, left, right)
		myOptimisedArray = make(map[int64]string, 1)
		myOptimisedArray[int64(right.n)] = arrayIndex
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		err = p.assignAug(e.Left, arrayIndex, fieldIndex, right)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		return right, nativeFunction, nil, myOptimisedArray

	case *CondExpr:
		// C-like ?: ternary conditional operator
		cond, _, err, _ := p.eval(e.Cond)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		if cond.boolean() {
			zz, _, err, _ := p.eval(e.True)
			return zz, nativeFunction, err, myOptimisedArray
		} else {
			yy, _, err, _ := p.eval(e.False)
			return yy, nativeFunction, err, myOptimisedArray
		}

	case *IndexExpr:
		// Read value from array by index
		index, err := p.evalIndex(e.Index)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		return p.getArrayValue(e.Array.Scope, e.Array.Index, index), nativeFunction, nil, myOptimisedArray

	case *CallExpr:
		// Call a builtin function
		callbuiltin, err := p.callBuiltin(e.Func, e.Args)
		return callbuiltin, nativeFunction, err, myOptimisedArray

	case *UnaryExpr:
		// Unary ! or + or -
		v, _, err, _ := p.eval(e.Value)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		return p.evalUnary(e.Op, v), nativeFunction, nil, myOptimisedArray

	case *InExpr:
		// "key in array" expression
		index, err := p.evalIndex(e.Index)
		if err != nil {
			return null(), nativeFunction, err, myOptimisedArray
		}
		array := p.arrays[p.getArrayIndex(e.Array.Scope, e.Array.Index)]
		_, ok := array[index]
		return boolean(ok), nativeFunction, nil, myOptimisedArray

	case *UserCallExpr:
		// Call user-defined or native Go function
		if e.Native {
			nativeFunction = true
			callnative, err := p.callNative(e.Index, e.Args)
			return callnative, nativeFunction, err, myOptimisedArray
		} else {
			calluser, err := p.callUser(e.Index, e.Args)
			return calluser, nativeFunction, err, myOptimisedArray
		}

	case *GetlineExpr:
		// Getline: read line from input
		var line string
		switch {
		case e.Command != nil:
			nameValue, _, err, _ := p.eval(e.Command)
			if err != nil {
				return null(), nativeFunction, err, myOptimisedArray
			}
			name := p.toString(nameValue)
			scanner, err := p.getInputScannerPipe(name)
			if err != nil {
				return null(), nativeFunction, err, myOptimisedArray
			}
			if !scanner.Scan() {
				if err := scanner.Err(); err != nil {
					return num(-1), nativeFunction, nil, myOptimisedArray
				}
				return num(0), nativeFunction, nil, myOptimisedArray
			}
			line = scanner.Text()
		case e.File != nil:
			nameValue, _, err, _ := p.eval(e.File)
			if err != nil {
				return null(), nativeFunction, err, myOptimisedArray
			}
			name := p.toString(nameValue)
			scanner, err := p.getInputScannerFile(name)
			if err != nil {
				return null(), nativeFunction, err, myOptimisedArray
			}
			if !scanner.Scan() {
				if err := scanner.Err(); err != nil {
					return num(-1), nativeFunction, nil, myOptimisedArray
				}
				return num(0), nativeFunction, nil, myOptimisedArray
			}
			line = scanner.Text()
		default:
			var err error
			line, err = p.nextLine()
			if err == io.EOF {
				return num(0), nativeFunction, nil, myOptimisedArray
			}
			if err != nil {
				return num(-1), nativeFunction, nil, myOptimisedArray
			}
		}
		if e.Var != nil {
			err := p.setVar(e.Var.Scope, e.Var.Index, str(line))
			if err != nil {
				return null(), nativeFunction, err, myOptimisedArray
			}
		} else {
			p.setLine(line)
		}
		return num(1), nativeFunction, nil, myOptimisedArray

	default:
		// Should never happen
		panic(fmt.Sprintf("unexpected expr type: %T", expr))
	}
}

func (p *interp) evalForAugAssign(expr Expr) (v value, arrayIndex string, fieldIndex int, err error) {
	switch expr := expr.(type) {
	case *VarExpr:
		v = p.getVar(expr.Scope, expr.Index)
	case *IndexExpr:
		arrayIndex, err = p.evalIndex(expr.Index)
		if err != nil {
			return null(), "", 0, err
		}
		v = p.getArrayValue(expr.Array.Scope, expr.Array.Index, arrayIndex)
	case *FieldExpr:
		index, _, err, _ := p.eval(expr.Index)
		if err != nil {
			return null(), "", 0, err
		}
		fieldIndex = int(index.num())
		v, err = p.getField(fieldIndex)
		if err != nil {
			return null(), "", 0, err
		}
	}
	return v, arrayIndex, fieldIndex, nil
}

func (p *interp) assignAug(expr Expr, arrayIndex string, fieldIndex int, v value) error {
	switch expr := expr.(type) {
	case *VarExpr:
		return p.setVar(expr.Scope, expr.Index, v)
	case *IndexExpr:
		p.setArrayValue(expr.Array.Scope, expr.Array.Index, arrayIndex, v)
	default: // *FieldExpr
		return p.setField(fieldIndex, p.toString(v))
	}
	return nil
}

// Get a variable's value by index in given scope
func (p *interp) getVar(scope VarScope, index int) value {
	switch scope {
	case ScopeGlobal:
		return p.globals[index]
	case ScopeLocal:
		return p.frame[index]
	default: // ScopeSpecial
		switch index {
		case V_NF:
			p.ensureFields()
			return num(float64(p.numFields))
		case V_NR:
			return num(float64(p.lineNum))
		case V_RLENGTH:
			return num(float64(p.matchLength))
		case V_RSTART:
			return num(float64(p.matchStart))
		case V_FNR:
			return num(float64(p.fileLineNum))
		case V_ARGC:
			return num(float64(p.argc))
		case V_CONVFMT:
			return str(p.convertFormat)
		case V_FILENAME:
			return str(p.filename)
		case V_FS:
			return str(p.fieldSep)
		case V_OFMT:
			return str(p.outputFormat)
		case V_OFS:
			return str(p.outputFieldSep)
		case V_ORS:
			return str(p.outputRecordSep)
		case V_RS:
			return str(p.recordSep)
		case V_SUBSEP:
			return str(p.subscriptSep)
		default:
			panic(fmt.Sprintf("unexpected special variable index: %d", index))
		}
	}
}

// Set a variable by name (specials and globals only)
func (p *interp) setVarByName(name, value string) error {
	index := float64(SpecialVarIndex(name))
	if index > 0 {
		return p.setVar(ScopeSpecial, int(index), numStr(value))
	}
	index, ok := p.program.Scalars[name]
	if ok {
		return p.setVar(ScopeGlobal, int(index), numStr(value))
	}
	// Ignore variables that aren't defined in program
	return nil
}

func (p *interp) setVariable(offset int, operation string) {

}

// Set a variable by index in given scope to given value
func (p *interp) setVar(scope VarScope, index int, v value) error {
	switch scope {
	case ScopeGlobal:
		p.globals[index] = v
		return nil
	case ScopeLocal:
		p.frame[index] = v
		return nil
	default: // ScopeSpecial
		switch index {
		case V_NF:
			numFields := int(v.num())
			if numFields < 0 {
				return newError("NF set to negative value: %d", numFields)
			}
			if numFields > maxFieldIndex {
				return newError("NF set too large: %d", numFields)
			}
			p.ensureFields()
			p.numFields = numFields
			if p.numFields < len(p.fields) {
				p.fields = p.fields[:p.numFields]
			}
			for i := len(p.fields); i < p.numFields; i++ {
				p.fields = append(p.fields, "")
			}
			p.line = strings.Join(p.fields, p.outputFieldSep)
		case V_NR:
			p.lineNum = int(v.num())
		case V_RLENGTH:
			p.matchLength = int(v.num())
		case V_RSTART:
			p.matchStart = int(v.num())
		case V_FNR:
			p.fileLineNum = int(v.num())
		case V_ARGC:
			p.argc = int(v.num())
		case V_CONVFMT:
			p.convertFormat = p.toString(v)
		case V_FILENAME:
			p.filename = p.toString(v)
		case V_FS:
			p.fieldSep = p.toString(v)
			if utf8.RuneCountInString(p.fieldSep) > 1 {
				re, err := regexp.Compile(p.fieldSep)
				if err != nil {
					return newError("invalid regex %q: %s", p.fieldSep, err)
				}
				p.fieldSepRegex = re
			}
		case V_OFMT:
			p.outputFormat = p.toString(v)
		case V_OFS:
			p.outputFieldSep = p.toString(v)
		case V_ORS:
			p.outputRecordSep = p.toString(v)
		case V_RS:
			sep := p.toString(v)
			if len(sep) > 1 {
				return newError("RS must be at most 1 char")
			}
			p.recordSep = sep
		case V_SUBSEP:
			p.subscriptSep = p.toString(v)
		default:
			panic(fmt.Sprintf("unexpected special variable index: %d", index))
		}
		return nil
	}
}

// Determine the index of given array into the p.arrays slice. Global
// arrays are just at p.arrays[index], local arrays have to be looked
// up indirectly.
func (p *interp) getArrayIndex(scope VarScope, index int) int {
	if scope == ScopeGlobal {
		return index
	} else {
		return p.localArrays[len(p.localArrays)-1][index]
	}
}

// Get a value from given array by key (index)
func (p *interp) getArrayValue(scope VarScope, arrayIndex int, index string) value {
	resolved := p.getArrayIndex(scope, arrayIndex)
	array := p.arrays[resolved]
	v, ok := array[index]
	if !ok {
		// Strangely, per the POSIX spec, "Any other reference to a
		// nonexistent array element [apart from "in" expressions]
		// shall automatically create it."
		array[index] = v
	}
	return v
}

// Set a value in given array by key (index)
func (p *interp) setArrayValue(scope VarScope, arrayIndex int, index string, v value) {
	resolved := p.getArrayIndex(scope, arrayIndex)
	p.arrays[resolved][index] = v
}

// Get the value of given numbered field, equivalent to "$index"
func (p *interp) getField(index int) (value, error) {
	if index < 0 {
		return null(), newError("field index negative: %d", index)
	}
	if index == 0 {
		return numStr(p.line), nil
	}
	p.ensureFields()
	if index > len(p.fields) {
		return str(""), nil
	}
	return numStr(p.fields[index-1]), nil
}

// Sets a single field, equivalent to "$index = value"
func (p *interp) setField(index int, value string) error {
	if index == 0 {
		p.setLine(value)
		return nil
	}
	if index < 0 {
		return newError("field index negative: %d", index)
	}
	if index > maxFieldIndex {
		return newError("field index too large: %d", index)
	}
	// If there aren't enough fields, add empty string fields in between
	p.ensureFields()
	for i := len(p.fields); i < index; i++ {
		p.fields = append(p.fields, "")
	}
	p.fields[index-1] = value
	p.numFields = len(p.fields)
	p.line = strings.Join(p.fields, p.outputFieldSep)
	return nil
}

// Convert value to string using current CONVFMT
func (p *interp) toString(v value) string {
	return v.str(p.convertFormat)
}

// Compile regex string (or fetch from regex cache)
func (p *interp) compileRegex(regex string) (*regexp.Regexp, error) {
	if re, ok := p.regexCache[regex]; ok {
		return re, nil
	}
	re, err := regexp.Compile(regex)
	if err != nil {
		return nil, newError("invalid regex %q: %s", regex, err)
	}
	// Dumb, non-LRU cache: just cache the first N regexes
	if len(p.regexCache) < maxCachedRegexes {
		p.regexCache[regex] = re
	}
	return re, nil
}

// Evaluate simple binary expression and return result
func (p *interp) evalBinary(op Token, l, r value) (value, error) {
	// Note: cases are ordered (very roughly) in order of frequency
	// of occurrence for performance reasons. Benchmark on common code
	// before changing the order.
	switch op {
	case ADD:
		return num(l.num() + r.num()), nil
	case SUB:
		return num(l.num() - r.num()), nil
	case EQUALS:
		if l.isTrueStr() || r.isTrueStr() {
			return boolean(p.toString(l) == p.toString(r)), nil
		} else {
			return boolean(l.n == r.n), nil
		}
	case LESS:
		if l.isTrueStr() || r.isTrueStr() {
			return boolean(p.toString(l) < p.toString(r)), nil
		} else {
			return boolean(l.n < r.n), nil
		}
	case LTE:
		if l.isTrueStr() || r.isTrueStr() {
			return boolean(p.toString(l) <= p.toString(r)), nil
		} else {
			return boolean(l.n <= r.n), nil
		}
	case CONCAT:
		return str(p.toString(l) + p.toString(r)), nil
	case MUL:
		return num(l.num() * r.num()), nil
	case DIV:
		rf := r.num()
		if rf == 0.0 {
			return null(), newError("division by zero")
		}
		return num(l.num() / rf), nil
	case GREATER:
		if l.isTrueStr() || r.isTrueStr() {
			return boolean(p.toString(l) > p.toString(r)), nil
		} else {
			return boolean(l.n > r.n), nil
		}
	case GTE:
		if l.isTrueStr() || r.isTrueStr() {
			return boolean(p.toString(l) >= p.toString(r)), nil
		} else {
			return boolean(l.n >= r.n), nil
		}
	case NOT_EQUALS:
		if l.isTrueStr() || r.isTrueStr() {
			return boolean(p.toString(l) != p.toString(r)), nil
		} else {
			return boolean(l.n != r.n), nil
		}
	case MATCH:
		re, err := p.compileRegex(p.toString(r))
		if err != nil {
			return null(), err
		}
		matched := re.MatchString(p.toString(l))
		return boolean(matched), nil
	case NOT_MATCH:
		re, err := p.compileRegex(p.toString(r))
		if err != nil {
			return null(), err
		}
		matched := re.MatchString(p.toString(l))
		return boolean(!matched), nil
	case POW:
		return num(math.Pow(l.num(), r.num())), nil
	case MOD:
		rf := r.num()
		if rf == 0.0 {
			return null(), newError("division by zero in mod")
		}
		return num(math.Mod(l.num(), rf)), nil
	default:
		panic(fmt.Sprintf("unexpected binary operation: %s", op))
	}
}

// Evaluate unary expression and return result
func (p *interp) evalUnary(op Token, v value) value {
	switch op {
	case SUB:
		return num(-v.num())
	case NOT:
		return boolean(!v.boolean())
	case ADD:
		return num(v.num())
	default:
		panic(fmt.Sprintf("unexpected unary operation: %s", op))
	}
}

// Perform an assignment: can assign to var, array[key], or $field
func (p *interp) assign(left Expr, right value) error {
	switch left := left.(type) {
	case *VarExpr:
		return p.setVar(left.Scope, left.Index, right)
	case *IndexExpr:
		index, err := p.evalIndex(left.Index)
		if err != nil {
			return err
		}
		p.setArrayValue(left.Array.Scope, left.Array.Index, index, right)
		return nil
	case *FieldExpr:
		index, _, err, _ := p.eval(left.Index)
		if err != nil {
			return err
		}
		return p.setField(int(index.num()), p.toString(right))
	}
	// Shouldn't happen
	panic(fmt.Sprintf("unexpected lvalue type: %T", left))
}

// Evaluate an index expression to a string. Multi-valued indexes are
// separated by SUBSEP.
func (p *interp) evalIndex(indexExprs []Expr) (string, error) {
	// Optimize the common case of a 1-dimensional index
	if len(indexExprs) == 1 {
		v, _, err, _ := p.eval(indexExprs[0])
		if err != nil {
			return "", err
		}
		return p.toString(v), nil
	}

	// Up to 3-dimensional indices won't require heap allocation
	indices := make([]string, 0, 3)
	for _, expr := range indexExprs {
		v, _, err, _ := p.eval(expr)
		if err != nil {
			return "", err
		}
		indices = append(indices, p.toString(v))
	}
	return strings.Join(indices, p.subscriptSep), nil
}
