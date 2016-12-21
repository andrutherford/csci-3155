package jsy.student

object Lab3 extends jsy.util.JsyApplication {
  import jsy.lab3.Parser
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * Andrew Rutherford
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
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
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */

  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

  /*
   * The implementations of these helper functions for conversions can come
   * Lab 2. The definitions for the new value type for Function are given.
   */

  //def allDigits(x: String) = x forall Character.isDigit

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => try s.toDouble catch { case _: Throwable => Double.NaN }
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) if (n compare 0.0) == 0 || (n compare -0.0) == 0 || n.isNaN => false
      case N(_) => true
      case B(b) => b
      case Undefined => false
      case S(s) => if (s == "") false else true
      case Function(_, _, _) => true
      case _ => ???
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case B(b) => b.toString
      case S(s) => s
        // Here in toStr(Function(_, _, _)), we will deviate from Node.js that returns the concrete syntax
        // of the function (from the input program).
      case Function(_, _, _) => "function"
      case _ => ???
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      //Case for two strings
      case (S(s1), S(s2)) => (bop: @unchecked) match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
    }
      //Anything that is not a string is passed into toNumber and evaluated as numbers
      case (_,_) => val (n1, n2) = (toNumber(v1), toNumber(v2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
      }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */

  /*
   * This code is a reference implementation of JavaScripty without
   * strings and functions (i.e., Lab 2).  You are to welcome to
   * replace it with your code from Lab 2.
   */
  def eval(env: Env, e: Expr): Expr = {
    def eToN(e: Expr): Double = toNumber(eval(env, e))
    def eToB(e: Expr): Boolean = toBoolean(eval(env, e))
    def eToVal(e: Expr): Expr = eval(env, e)
    e match {
      /* Base Cases */
      case N(_) | B(_) | S(_) | Undefined | Function(_, _, _) => e
      case Var(x) => get(env, x)

      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined

      //Unary Cases
      case Unary(uop, e1) => uop match {
        case Neg => N(-1 * toNumber(eToVal(e1)))
        case Not => B(!toBoolean(eToVal(e1)))
      }

      //Arithmetic Cases
      case Binary(Plus, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), S(s2)) => S(s1 + s2)
        case (S(s1), _) => S(s1 + toStr(e2))
        case (_, S(s2)) => S(toStr(e1) + s2)
        case (_, _) => N(toNumber(e1) + toNumber(e2)) }
      case Binary(Minus, e1, e2) => N(toNumber(e1) - toNumber(e2))
      case Binary(Times, e1, e2) => N(toNumber(e1) * toNumber(e2))
      case Binary(Div, e1, e2) => N(toNumber(e1) / toNumber(e2))

      //Equality Cases
      case Binary(Eq, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), S(s2)) => B(s1 == s2)
        case (B(b1), B(b2)) => B(b1 == b2)
        case (N(n1), N(n2)) => B(n1 == n2)
        case (Undefined, Undefined) => B(true)
        case (_, _) => B(false) }
      case Binary (Ne, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), S(s2)) => B(s1 != s2)
        case (B(b1), B(b2)) => B(b1 != b2)
        case (N(n1), N(n2)) => B(n1 != n2)
        case (Undefined, Undefined) => B(false)
        case (_, _) => B(true) }

      //Comparison cases
      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => B(inequalityVal(bop, eToVal(e1), eToVal(e2)))

      //And/Or/Seq cases
      case Binary (And, e1v, e2v) => if (toBoolean(e1v)) e2v else e1v
      case Binary (Or, e1v, e2v) => if (toBoolean(e1v)) e1v else e2v
      case Binary (Seq, e1v, e2v) => e1v; e2v

      //If case
      case If  (e1, e2, e3) => {
        val v1 = eToVal(e1)
        if (toBoolean(v1)) eToVal(e2) else eToVal(e3) }

      //Constdecl
      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)


      case Call(e1, e2) => (eToVal(e1), eToVal(e2)) match {

        //Case that function has a name
        case (Function(None, x, e3), e2) => eval(extend(env, x, eval(env, e2)), e3)

        //Case that function does not have a name
        case (Function(Some(s), x, e3), e2) => eval(extend(extend(env, s, e1), x, eval(env, e2)), e3)
      }
    }
  }
    

  /* Small-Step Interpreter with Static Scoping */

  //For  every instance of x, replace it with v in the expression e

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */

    //subst(e1) is the same thing as substitute(e1, v, x)
    def subst(e: Expr): Expr = substitute(e, v, x)
    /* Body */
    e match {
      case N(_) | B(_) | Undefined | S(_) => e

      //If e is the function and it contains string x, return it
      //Otherwise, substitute into the function
      case Function (p ,s , e1) => if ((Some(x) == p) || (x == s)) return e else return Function (p, s, subst(e1))

      case Binary (op, e1, e2) => op match {
        case (Eq|Ne) => e1 match {
          case Function(x, y, z) => throw new DynamicTypeError(e)
          case _ => return Binary( op, substitute(e1, v, x), substitute(e2, v, x))
        }
      }
      case Unary (op, e1) => return Unary(op, subst(e1))
      case Call(e1, e2) => return Call(subst(e1), subst(e2))
      case If(e1, e2, e3) => return If(subst(e1), subst(e2), subst(e3))
      case Print(e1) => Print(subst(e1))
      case Var(t) => if (t == x) return v else e
      case ConstDecl(y, e1, e2) => ConstDecl(y, subst(e1), if (x == y) e2 else subst(e2))
      case _ => throw new UnsupportedOperationException

    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined

      //DoNeg
      case Unary(Neg, v1) => N(-toNumber(v1))
      //DoNot
      case Unary(Not, v1) => B(!toBoolean(v1))
      //DoSeq
      case Binary(Seq, v1, e2) if (isValue(v1)) => e2
      //DoAnd
      case Binary(And, v1, e2) if isValue(v1) => if (toBoolean(v1)) e2 else v1
      //DoOr
      case Binary(Or, v1, e2) if isValue(v1) => if (toBoolean(v1)) v1 else e2
      //DoIf
      case If(v1, e2, e3) if (isValue(v1)) => if (toBoolean(v1)) e2 else e3
      //DoConst: If v1 is a value, in e2,replace all occurrences of v1 with x
      case ConstDecl(x, v1, e2) if (isValue(v1)) => substitute(e2, v1, x)

      //DoArith - Plus
      case Binary(Plus, e1, e2) if (isValue(e1) && isValue(e2)) => (e1, e2) match {
        case (S(e1), _) => S(e1 + toStr(e2))
        case (_, S(e2)) => S(toStr(e1) + e2)
        case (N(e1), N(e2)) => N(e1 + e2)
        case _ => N(toNumber(e1) + toNumber(e2))
      }

      //DoArith
      case Binary(bop, e1, e2) if (isValue(e1) && isValue(e2)) => bop match {
        case Minus => N(toNumber(e1) - toNumber(e2))
        case Times => N(toNumber(e1) * toNumber(e2))
        case Div => N(toNumber(e1) / toNumber(e2))
      }

      //DoEquality
      case Binary(Eq, v1, v2) => v1 match {
        case Function(_, _, _) => throw new DynamicTypeError(v1)
        case _ => v2 match {
          case Function(_, _, _) => throw new DynamicTypeError(v2)
          case _ => B(v1 == v2)
        }
      }
      case Binary(Ne, v1, v2) => v1 match {
        case Function(_, _, _) => throw new DynamicTypeError(v1)
        case _ => v2 match {
          case Function(_, _, _) => throw new DynamicTypeError(v2)
          case _ => B(v1 != v2)
        }
      }

      //DoInequality
      case Binary(bop@(Lt | Le | Gt | Ge), e1, e2) => B(inequalityVal(bop, e1, e2))

      //DoCall
      case Call(v1, v2) if (isValue(v1) && isValue(v2)) => v1 match {
        case Function(None, x, ebody) => substitute(ebody, v2, x)
        case Function(Some(name), x, ebody) => {
          val v3body = substitute(ebody, v2, x)
          substitute(v3body, Function(Some(name), x, ebody), name)
        }
        case _ => throw new DynamicTypeError(v1)

      }







      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      //SearchUnary
      case Unary(op, e1) => Unary(op, step(e1))
      //SearchBinary
      case Binary(op, e1, e2) => Binary(op, step(e1), e2)

      //SearchEquality
      case Binary(op, v1, e2) if (isValue(v1)) => (op, v1, e2) match {
        case (Eq, v1, Function(_, _, _)) => throw new DynamicTypeError(e2)
        case (Eq, Function(_, _, _), e2) => throw new DynamicTypeError(v1)
        case (Ne, v1, Function(_, _, _)) => throw new DynamicTypeError(e2)
        case (Ne, Function(_, _, _), e2) => throw new DynamicTypeError(v1)
        case _ => Binary(op, v1, step(e2))

      }
      //SearchBinaryArith
      case Binary(op, v1, e2) if (isValue(v1)) => Binary(op, v1, step(e2))

      //SearchIf
      case If(e1, e2, e3) => If(step(e1), e2, e3)

      //SearchConst
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)

      //SearchCall
      case Call(e1, e2) => Call(step(e1), e2)
      case Call(v1, e2) if (isValue(v1)) => Call(v1, step(e2))

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */

  //this.debug = true // uncomment this if you want to print debugging information

  // Interface to run your big-step interpreter starting from an empty environment and print out
  // the test input if debugging.
  def evaluate(e: Expr): Expr = {
    require(closed(e))
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with eval ...")
      println("\nExpression:\n  " + e)
    }
    val v = eval(emp, e)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def evaluate(s: String): Expr = evaluate(Parser.parse(s))

  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging.
  def iterateStep(e: Expr): Expr = {
    require(closed(e))
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (isValue(e)) e else loop(step(e), n + 1)
    }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val v = loop(e, 0)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(Parser.parse(s))

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }

    val expr =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }

    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }

}
