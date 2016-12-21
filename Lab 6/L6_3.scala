import jsy.lab6.JsyInterpreter
import jsy.lab6.JsyParser

object Lab6 extends jsy.util.JsyApplication {
  import jsy.lab6.ast._
  
  /*
   * lower in the parse tree, higher in precedence. 
   * CSCI 3155: Lab 6
   * <Samuel Volin>
   * 
   * Partner: <Cris Salazar>
   * Collaborators: <Alex Tsankov>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */

  
  /*** Regular Expression Parsing ***/
  import scala.util.parsing.combinator.Parsers
  import scala.util.parsing.input.Reader
  import scala.util.parsing.input.CharSequenceReader

  /* We define a recursive decent parser for regular expressions in
   * RegExprParser.
   * 
   * We derive RegExprParser from Parsers in the Scala library to make
   * use of it's handing of input (Input) and parsing results
   * (ParseResult).
   * 
   * The Parsers trait is actually a general purpose combinator parser
   * library that we will not use.
   * 
   * Grammar
   * 
   *   re ::= union
   *   union ::= intersect {| intersect}
   *   intersect ::= concat {& concat}
   *   concat ::= not {not}
   *   not ::= ~ not | star
   *   star ::= atom {*|+|?}
   *   atom ::= ! | # | c | . | ( re )
   * 
   */
  object RegExprParser extends Parsers {
    type Elem = Char

    /* The following items are the relevant pieces inherited from Parsers
     * 
     * type Input = Reader[Elem]
     * sealed abstract class ParseResult[+T] {
     *   val next: Input
     *   def map[U](f: T => U): ParseResult[U]
     * }
     * case class Success[+T](result: T, next: Input) extends ParseResult[T]
     * case class Failure(next: Input) extends ParseResult[Nothing]
     */
    //re simply calls union on the regular expression
    def re(next: Input): ParseResult[RegExpr] = union(next)

    def union(next: Input): ParseResult[RegExpr] = {
    println("union")
      intersect(next) match {
    
	      //success
	      case Success(r, next) => {
	        // unions ::= eps | intersect '|' unions
	        def unions(acc: RegExpr, next: Input): ParseResult[RegExpr] =
	          // matches eps (empty and successful
	          if (next.atEnd) Success(acc, next)
	          //pattern match
	          else (next.first, next.rest) match {
	            //the first character is a bar
	            case ('|', next) => intersect(next) match {
	              case Success(r, next) => unions(RUnion(acc, r), next)
	              case _ => Failure("expected intersect", next)
	            }
	            //matches the intersect '|' eps
	            case _ => Success(acc, next)
	          }
	        unions(r, next)
	      }
	      //failure
	      case _ => Failure("expected intersect", next)
	    }
    }
    def intersect(next: Input): ParseResult[RegExpr] = {
      println("Intersect")
      concat(next) match{
    
      case Success(r, next) => {
        def intersections(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next)
          else (next.first, next.rest) match {
            case ('&', next) => concat(next) match {
              case Success(r, next) => intersections(RIntersect(acc,r), next)
              case _ => Failure("expected concat", next)
            }
            case _ => Success(acc, next)
          }
        intersections(r, next)
      }
      //failure
      case _ => Failure("expected concat", next)
    }
    }
    
    // concat ::= not concats
    // concats ::= eps | not concats
    def concat(next: Input): ParseResult[RegExpr] = not(next) match {
    	case Success(r, next) => {
	        def concats(acc: RegExpr, next: Input): ParseResult[RegExpr] =
	          if (next.atEnd) Success(acc, next)
	          else not(next) match {
	              case Success(r, next) => concats(RConcat(acc, r), next)
	              case _ => Success(acc, next)
	          }
	        concats(r, next)
	    }
  		case fail => fail
    }

    //not ::= ‘~’ not | star
    //~cat, will select everything that doesn't have a c
    //such as "at" or "bat"
    
    
    def not(next: Input): ParseResult[RegExpr] = (next.first, next.rest) match {
     //check first for tilde)
    	case ('~', rest) => not(rest) match{
    	  //run not on the rest if there is a neg
        	case Success(r, next) => Success(RNeg(r), next)
        	//if we are succesful, return a success
        	case fail => fail
        	//otherwise fail
    	}
    	//or we go with star
    	case _ => star(next) match {
    	  	case Success(r, next) => Success(r, next)
    	  	case fail => fail
    	}
    }

    def star(next: Input): ParseResult[RegExpr] = atom(next) match {
      //we take the atom of the next
      case Success(r, next) => {
        def stars(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          //define a new function which takes the acc and next
          if (next.atEnd) Success(acc, next)
          //check if next is the end 
          else (next.first, next.rest) match {
            //else, check if there are any of the symbols we should have 
          	case ('+', next) => stars(RPlus(acc), next) 
          	case ('*', next) => stars(RStar(acc),next)
          	case ('?', next) => stars(ROption(acc), next)
            //run stars on the modified version 
            case _ => Success(acc, next)
            //otherwise we are successful
          }
        stars(r, next)
        //we need to run stars on 
      }
      case _ => Failure("no atom", next)
    }

    /* This set is useful to check if a Char is/is not a regular expression
       meta-language character.  Use delimiters.contains(c) for a Char c. */
    val delimiters = Set('|', '&', '~', '*', '+', '?', '!', '#', '.', '(', ')')

    //went over in class
    def atom(next: Input): ParseResult[RegExpr] = {
      if (next.atEnd) Failure("empty, not able to match", next)
      else (next.first, next.rest) match {
        case ('!', next) => Success(RNoString, next)
        case ('#', next) => Success(REmptyString, next)
        case ('.', next) => Success(RAnyChar, next)
        case ('(', next) => re(next) match {
          case Success(reast, next) => (next.first, next.rest) match {
            case (')', next) => Success(reast, next)
            case _ => Failure("expected )", next)
          }
          case fail => fail
        }
        case (c, next) if !delimiters.contains(c) => Success(RSingle(c), next)
        case _ => Failure("need an atom", next)
      }
    }

    /* External Interface */
    
    def parse(next: Input): RegExpr = re(next) match {
      case Success(r, next) if (next.atEnd) => r
      case Success(_, next) => throw new SyntaxError("remaining input", next.pos)
      case Failure(msg, next) => throw new SyntaxError(msg, next.pos)
    }

    def parse(s: String): RegExpr = parse(new CharSequenceReader(s))
  } 
  

  /*** Regular Expression Matching ***/
  
  //continuations capture what to be called later. It is a callback for your future reference.
  //they are useful when doing a backtracking search
  //they save computation on the chance failure means said computation doesn't need to be done.
  def retest(re: RegExpr, s: String): Boolean = {
    println("re: " + re.toString() + ", s: " + s)
    def test(re: RegExpr, chars: List[Char], sc: List[Char] => Boolean): Boolean = (re, chars) match {
      /* Basic Operators */
      //No string should not match anything, at all!
      case (RNoString, _) => false
      //emptystring matches # in the string. Check each character for the #
      case (REmptyString, _) => sc(chars)
      //single should match any one character c. If no string was provided, return false
      case (RSingle(_), Nil) => false
      //single should match a specific character c1. If the string begins with c2, compare c1 and c2.
      //if c1 == c2, invoke the success continuation. Otherwise return false
      case (RSingle(c1), c2 :: t) => if (c1 == c2) sc(t) else false
      //re1 and re2 should match, and they should match adjacent to each other 
      case (RConcat(re1, re2), _) => test(re1, chars, { remchars => test(re2, remchars, sc) })
      //either re1 or re2 should match
      case (RUnion(re1, re2), _) => test(re1, chars, sc) || test(re2, chars, sc)
      case (RStar(re1), _) => {
        sc(chars) || 
        //chars.forall( c => test(RStar(re1), c::Nil, sc))
        //test(re1, chars, {remchars => test(RStar(re1), remchars, sc)})
        test(re1, chars, {remchars => if (remchars.size >= chars.size) false else test(RStar(re1), remchars, sc)})
      }

      /* Extended Operators */
      case (RAnyChar, Nil) => false
      case (RAnyChar, _ :: t) => sc(t)
      case (RPlus(re1), _) => test(RConcat(re1, RStar(re1)), chars, sc) //chang reccomended solution
      //case (RPlus(re1), _) => test(re1, chars, {remchars => remchars.forall{ c => test(RStar(re1), c::Nil, sc)} })//chars.forall( c => test(re1, c::Nil, sc))
      case (ROption(re1), _) => if (chars.isEmpty) true else test(re1, chars, sc)

      /***** Extra Credit Cases *****/
      case (RIntersect(re1, re2), _) => test(re1, chars, sc) && test(re2, chars, sc)
      case (RNeg(re1), _) =>  !test(re1, chars, sc)//defs not correct
    }
    test(re, s.toList, { chars => chars.isEmpty })
  }
  
  /*** JavaScripty Interpreter ***/

  /* This part is optional and only for fun.
   * 
   * If you want your own complete JavaScripty interpreter, you can copy your
   * Lab 5 interpreter here and extend it for the Lab 6 constructs.
   * 
   * By default, a reference JavaScripty interpreter will run using your
   * regular expression tester.
   */
  object MyInterpreter extends jsy.lab6.Interpreter {
    /* Type checking. */
    def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ =
      throw new UnsupportedOperationException
    
    /* A small-step transition. */
    def stepre(retest: (RegExpr, String) => Boolean)(e: Expr): DoWith[Mem, Expr] = {
      def step(e: Expr): DoWith[Mem, Expr] = {
        require(!isValue(e), "stepping on a value: %s".format(e))
        throw new UnsupportedOperationException
      }
      step(e)
    }
  }


  /*** External Interfaces ***/

  this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(500) // comment this out or set to None to not bound the number of steps.

  var useReferenceRegExprParser = false /* set to true to use the reference parser */
  var useReferenceJsyInterpreter = true /* set to false to use your JavaScripty interpreter */

  this.flagOptions = this.flagOptions ++ List(
    ("ref-reparser", jsy.util.options.SetBool(b => useReferenceRegExprParser = b, Some(b => useReferenceRegExprParser == b)), "using the reference regular expression parser"),
    ("ref-jsyinterp", jsy.util.options.SetBool(b => useReferenceJsyInterpreter = b, Some(b => useReferenceJsyInterpreter == b)), "using the reference JavaScripty interpreter")
  )

  // Select the interpreter to use based on the useReferenceJsyInterpreter flag
  val interpreter: jsy.lab6.Interpreter =
    if (useReferenceJsyInterpreter) jsy.lab6.JsyInterpreter else MyInterpreter
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = interpreter.typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  
  case class TerminationError(e: Expr) extends Exception {
    override def toString = JsyParser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }

  def iterateStep(e: Expr): Expr = {
    require(closed(e), "not a closed expression: free variables: %s".format(freeVars(e)) )
    val step: Expr => DoWith[Mem, Expr] = interpreter.stepre(retest)
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(memempty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }
  
  // Select the parser to use based on the useReferenceRegExprParser flag
  def parser: JsyParser =
    if (useReferenceRegExprParser) new JsyParser else new JsyParser(RegExprParser.parse)

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      if (useReferenceRegExprParser) println("Parsing with reference RegExpr parser ...")
      else println("Parsing with your RegExpr parser ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        parser.parseFile(file)
      }} getOrElse {
        return
      }
    
    handle() {
      val t = inferType(expr)
    }
    
    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }
  
}