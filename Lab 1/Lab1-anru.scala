package jsy.student

object Lab1 extends jsy.util.JsyApplication {
  import jsy.lab1.Parser
  import jsy.lab1.ast._

  /*
   * CSCI 3155: Lab 1
   * Andrew Rutherford
   *
   * Partner: Justin McBride
   * Collaborators: Warren Ferrell
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
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

  /*
   * Example with a Unit Test
   *
   * A convenient, quick-and-dirty way to experiment, especially with small code
   * fragments, is to use the interactive Scala interpreter.
   *
   * To start the interactive Scala interpreter in IntelliJ, select Run Scala Console
   * from the Tools menu or the right-click menu for this file.
   *
   * To run a selection in the interpreter, highlight the code of interest
   * and select Send Selection to Scala Console from the right-click menu
   * or type Ctrl+Shift+X.
   *
   * Highlight the next few lines below to try it out.  The assertion passes, so
   * it appears that nothing happens.  You can uncomment the "bad test specification"
   * and see that a failed assert throws an exception.
   *
   * You can try calling 'plus' with some arguments, for example, plus(1,2).  You
   * should get a result something like 'res0: Int = 3'.
   *
   * As an alternative, the testPlus2 function takes an argument that has the form
   * of a plus function, so we can try it with different implementations.  For example,
   * uncomment the "testPlus2(badplus)" line, and you will see an assertion failure.
   *
   * While writing such testing snippets are convenient, it is not ideal.  For example,
   * the 'testPlus1()' call is run whenever this object is loaded, so in practice,
   * it should probably be deleted for "release".  A more robust way to maintain
   * unit tests is in a separate file.  For us, we use the convention of writing
   * tests in a file called LabXSpec.scala (i.e., Lab1Spec.scala for Lab 1).
   *
   * IntelliJ has another way to interactively run Scala expressions via Scala Worksheets.
   * A Scala Worksheet (e.g., Lab1Worksheet.sc) is code evaluated in the context of the
   * project with results for each expression shown inline.
   *
   */

  def plus(x: Int, y: Int): Int = x + y
  def testPlus1() {
    assert(plus(1,1) == 2)
    //assert(plus(1,1) == 3) // bad test specification
  }
  testPlus1()

  def badplus(x: Int, y: Int): Int = x - y
  def testPlus2(plus: (Int, Int) => Int) {
    assert(plus(1,1) == 2)
  }
  //testPlus2(badplus)

  /* Exercises */

  def abs(n: Double): Double = { if ( n < 0 ) -n else n }

  def xor(a: Boolean, b: Boolean): Boolean = {
    if ( a ) {
      if ( b ) false
      else true
    }
    else {
      if ( b ) true
      else false
    }
  }

  def repeat(s: String, n: Int): String = {
    if (n == 0) return ""
    else if (n < 0) throw new IllegalArgumentException;
    else {
      return s + repeat(s, n-1)
    }
  }

  def sqrtStep(c: Double, xn: Double): Double = {
    xn - ( ((xn*xn) - c) / (2 * xn ) )
  }

  def sqrtN(c: Double, x0: Double, n: Int): Double = {
    // c = number we want sqrt of
    // x0 = initial guess for newton's method
    // n = number of times to recurse, bigger=better
    require( c >= 0 && n >= 0 )
    if ( n == 0 ) return x0
    return sqrtStep(c, sqrtN(c, x0, n-1))

  }

  def sqrtErr(c: Double, x0: Double, epsilon: Double): Double = {
    if ( epsilon <= 0 ) throw new IllegalArgumentException;
    if ( abs((x0 * x0) - c) < epsilon ) return x0
    return sqrtErr(c, sqrtStep(c, x0), epsilon)
  }

  def sqrt(c: Double): Double = {
    require(c >= 0)
    if (c == 0) 0 else sqrtErr(c, 1.0, 0.0001)
  }

  /* Search Tree */

  sealed abstract class SearchTree
  case object Empty extends SearchTree
  case class Node(l: SearchTree, d: Int, r: SearchTree) extends SearchTree

  def repOk(t: SearchTree): Boolean = {
    def check(t: SearchTree, min: Int, max: Int): Boolean = t match {
      case Empty => true
      case Node(l, d, r) => {
        if (
             d >= min &&
             d < max &&
             check(l, min, d) &&
             check(r, d, max) ) true
        else false
      }
    }
    check(t, Int.MinValue, Int.MaxValue)
  }

  def insert(t: SearchTree, n: Int): SearchTree = {
    t match {
      case Empty => {
        Node(Empty, n, Empty)
      }
      case Node(l, d, r) => {
        if ( n < d ) {
          Node( insert(l, n), d, r )
        }
        else {
          Node( l, d, insert(r, n) )
        }
      }
    }
  }

  def deleteMin(t: SearchTree): (SearchTree, Int) = {
    require(t != Empty)
    (t: @unchecked) match {
      case Node(Empty, d, r) => (r, d)
      case Node(l, d, r) =>
        val (l1, m) = deleteMin(l)
        ( Node( l1, d, r ), m )
    }
  }

  def delete(t: SearchTree, n: Int): SearchTree = {
    t match {
      case Node(Empty, d, Empty) => {
        if ( d == n ) Empty
        else t
      }
      case Node(l, d, Empty) => {
        if ( d == n ) l
        else if ( d > n ) delete(l, n)
        else l
      }

      case Node(Empty, d, r) => {
        if ( d == n ) r
        else if ( d <= n ) delete(r, n)
        else r
      }

      case Node(l, d, r) => {
        if ( d == n ) {
          val (newR, m) = deleteMin(r)
          newR match {
            case Empty => Node(l, m, Empty)
            case Node(_, _, _) => Node(l, m, delete(newR, m))
          }
        }
        else if ( n < d ) {
          Node(delete(l, n), d, r)
        } else {
          Node(l, d, delete(r, n))
        }
      }
    }
  }

  /* JavaScripty */

  def eval(e: Expr): Double = e match {
    case N(n) => {
      n
    }
    case Binary(bop, e1, e2) => {
      bop match {
        case Plus => {
          eval(e1) + eval(e2)
        }
        case Minus => {
          eval(e1) - eval(e2)
        }
        case Times => {
          eval(e1) * eval(e2)
        }
        case Div => {
          val val1 = eval(e1)
          val val2 = eval(e2)

          if (val2 == 0) {
            if ( val1 >= 0 ) Double.PositiveInfinity
            else Double.NegativeInfinity
          }
          else val1 / val2
        }
      }
    }
    case Unary(uop, e1) => {
      uop match {
        case Neg => {
          eval(e1) * -1
        }
      }
    }
    case _ => throw new UnsupportedOperationException
  }

 // Interface to run your interpreter from a string.  This is convenient
 // for unit testing.
 def eval(s: String): Double = eval(Parser.parse(s))



 /* Interface to run your interpreter from the command-line.  You can ignore the code below. */

 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println(s"\nExpression AST:\n  ${expr}")
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

    println(v)
  }

}
