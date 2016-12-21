package jsy.student

object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * Andrew Rutherford
   * 
   * Partner: Warren Farrel
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the '???' expression with  your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The ???
   * is a Scala expression that throws the exception scala.NotImplementedError.
   *
   */

  /* We represent a variable environment as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */

  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def allDigits(x: String) = x forall Character.isDigit

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if (b) return 1 else return 0
      case S(s) => if (allDigits(s)) s.toDouble else if (s == "") return 0 else Double.NaN
      case Undefined => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if (n.isNaN()) return false else return (n != 0)
      case S(s) => if(s == "") false else true
      case Undefined => return false
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case B(b) => if (b) "true" else "false"
      case Undefined => "undefined"
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)
    

    e match {
      /* Base Cases - If expression cannot be evaluated further */
      case N(n) => N(n)
      case B(b) => B(b)
      case S(s) => S(s)
      case Var(x) => env(x)
      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)
      case Undefined => return Undefined

      /* Inductive Cases */
      case Print(e1) => println(pretty(eToVal(e1))); Undefined
      case Unary(uop, e1) => uop match {
        case Neg => N(-1 * toNumber(eToVal(e1)))
        case Not => B(!toBoolean(eToVal(e1)))
      }

      case Binary(bop, e1, e2) => val (e1v, e2v) = (eToVal(e1), eToVal(e2))
        bop match {
          case Plus => (e1v, e2v) match {
            case (S(s1), S(s2)) => S(s1 + s2)
            case (S(s1), _) => S(s1 + toStr(e2v))
            case (_, S(s2)) => S(toStr(e1v) + s2)
            case (_, _) => N(toNumber(e1v) + toNumber(e2v))
          }
          case Minus => N(toNumber(e1v) - toNumber(e2v))
          case Times => N(toNumber(e1v) * toNumber(e2v))
          case Div => N(toNumber(e1v) / toNumber(e2v))

          case Eq => (e1v, e2v) match {
            case (S(s1), S(s2)) => B(s1 == s2)
            case (B(b1), B(b2)) => B(b1 == b2)
            case (N(n1), N(n2)) => B(n1 == n2)
            case (Undefined, Undefined) => B(true)
            case (_, _) => B(false)
          }
          case Ne => (e1v, e2v) match {
            case (S(s1), S(s2)) => B(s1 != s2)
            case (B(b1), B(b2)) => B(b1 != b2)
            case (N(n1), N(n2)) => B(n1 != n2)
            case (Undefined, Undefined) => B(false)
            case (_, _) => B(true)
          }
          case Lt => (e1v, e2v) match {
            case ((S(s1)), S(s2)) => B(s1 < s2)
            case ((S(s1)), e2v) => B(s1 < toStr(e2v))
            case (e1v, S(s2)) => B(toStr(e1v) < s2)
            case (Undefined, Undefined) => B(false)
            case (Undefined, _) => B(false)
            case (_, Undefined) => B(false)
            case (_, _) => B(toNumber(e1v) <  toNumber(e2v))

          }
          case Le => (e1v, e2v) match {
            case ((S(s1)), S(s2)) => B((s1 < s2) || (s1 == s2))
            case ((S(s1)), e2v) => B((s1 < toStr(e2v)) || (s1 == toStr(e2v)))
            case (e1v, S(s2)) => B((toStr(e1v) < s2) || (toStr(e1v) == s2))
            case (Undefined, Undefined) => B(false)
            case (Undefined, _) => B(false)
            case (_, Undefined) => B(false)
            case (_, _) => B((toNumber(e1v) <  toNumber(e2v)) || (toNumber(e1v) == toNumber(e2v)))
          }

          case Gt => (e1v, e2v) match {
            case ((S(s1)), S(s2)) => B(s1 > s2)
            case ((S(s1)), e2v) => B(s1 > toStr(e2v))
            case (e1v, S(s2)) => B(toStr(e1v) > s2)
            case (Undefined, Undefined) => B(false)
            case (Undefined, _) => B(false)
            case (_, Undefined) => B(false)
            case (_, _) => B(toNumber(e1v) >  toNumber(e2v))
          }
          case Ge => (e1v, e2v) match {
            case ((S(s1)), S(s2)) => B((s1 > s2) || (s1 == s2))
            case ((S(s1)), e2v) => B((s1 > toStr(e2v)) || (s1 == toStr(e2v)))
            case (e1v, S(s2)) => B((toStr(e1v) > s2) || (toStr(e1v) == s2))
            case (Undefined, Undefined) => B(false)
            case (Undefined, _) => B(false)
            case (_, Undefined) => B(false)
            case (_, _) => B((toNumber(e1v) >  toNumber(e2v)) || (toNumber(e1v) == toNumber(e2v)))
          }

          case And => (e1v, e2v) match {
            //Evaluates to:
            //e1v if e1v is false - e2v is not evaluated
            //e2v if e1v is true
            case (_,_) => if (toBoolean(e1v)) e2v else e1v
          }
          case Or => (e1v, e2v) match {
            //Evaluates to:
            //e1v if e1v is true
            //e2v if e1v is false
            case (_, _) => if (toBoolean(e1v)) e1v else e2v
          }
          case Seq => (e1v, e2v) match {
            case (_, _) => e1v; e2v
          }
        }
      case If (e1, e2, e3) => {
        val v1 = eToVal(e1)
        if (toBoolean(v1)) eToVal(e2) else eToVal(e3)
      }
      case Print (e1) => {
        Print(eToVal(e1))
      }
    }
  }

  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

  /* Interface to run your interpreter from the command-line.  You can ignore what's below. */
  def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

     println(pretty(v))
  }

}
