package jsy.student

object Lab3 extends jsy.util.JsyApplication {
  import jsy.lab3.ast._

  /*

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

  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }

  def allDigits(x: String) = x forall Character.isDigit

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if (b) 1 else 0
      case Undefined => Double.NaN
      case S(s) => if (allDigits(s)) s.toDouble else if (s == "") return 0 else Double.NaN
      case Function(_, _, _) => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case N(n) => if (n.isNaN()) return false else return (n != 0)
      case S(s) => if(s == "") false else true
      case Undefined => return false
      case Function(_, _, _) => true
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case B(b) => if (b) "true" else "false"
      case Undefined => "undefined"
      case Function(_, _, _) => "function"
    }
  }

  def isEqual(v1: Expr, v2: Expr) : Boolean = {
    require(isValue(v1) && isValue(v2))
    (v1,v2) match {
      case (N(a),N(b)) => (a == b)
      case (B(a),B(b)) => (a == b)
      case (S(a),S(b)) => (a == b)
      case (Undefined,Undefined) => true
      case _ => false
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1))
    require(isValue(v2))
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case _ =>
        val (n1, n2) = (toNumber(v1), toNumber(v2))
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

      case Unary(uop, e1) => uop match {
        case Neg => N(-1 * eToN(e1))
        case Not => B(!eToB(e1))
      }

      case Binary(Plus, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), v2) => S(s1 + toStr(v2))
        case (v1, S(s2)) => S(toStr(v1) + s2)
        case (v1, v2) => N(toNumber(v1) + toNumber(v2))
        case _ => ???
      }
      case Binary(Minus, e1, e2) => N(eToN(e1) - eToN(e2))
      case Binary(Times, e1, e2) => N(eToN(e1) * eToN(e2))
      case Binary(Div, e1, e2) => N(eToN(e1) / eToN(e2))

      case Binary(Eq, e1, e2) => e1 match {
        case Function(x, y, z) => throw new DynamicTypeError(e)
        case _ => e2 match {
          case Function(x, y, z) => throw new DynamicTypeError(e)
          case _ => B(eToVal(e1) == eToVal(e2))
        }
      }

      case Binary (Ne, e1, e2) => e1 match {
        case Function(x, y, z) => throw new DynamicTypeError(e)
        case _ => e2 match {
          case Function(x, y, z) => throw new DynamicTypeError(e)
          case _ => B(eToVal(e1) != eToVal(e2))
        }

      }
      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => B(inequalityVal(bop, eToVal(e1), eToVal(e2)))

      case Binary(And, e1, e2) =>
        val v1 = eToVal(e1)
        if (toBoolean(v1)) eToVal(e2) else v1
      case Binary(Or, e1, e2) =>
        val v1 = eToVal(e1)
        if (toBoolean(v1)) v1 else eToVal(e2)

      case Binary(Seq, e1, e2) => eToVal(e1); eToVal(e2)

      case If(e1, e2, e3) => if (eToB(e1)) eToVal(e2) else eToVal(e3)

      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)

      case Call(e1, e2) => eToVal(e1) match {
        case Function(None,x,e3) => eval(extend(env, x, eToVal(e2)), e3)
        case f @ Function(Some(fname),x,e) =>
          val env2 = extend(extend(env, fname, f), x, eToVal(e2))
          eval(env2, e)
        case _ => throw new DynamicTypeError(e1)
      }

      case _ => throw new UnsupportedOperationException
    }
  }


  /* Small-Step Interpreter with Static Scoping */

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    def subst(e: Expr): Expr = substitute(e, v, x)
    /* Body */
    e match {
      case Var(a) if a == x => v
      case N(_) | B(_) | Undefined | S(_) | Var(_) => e
      case Function(None,a,e1) =>
        if (x == a) e else Function(None,a,subst(e1))
      case Function(Some(p),a,e1) =>
        if (x == a || x == p) e else Function(Some(p),a,subst(e1))
      case ConstDecl(x,e1,e2) => ConstDecl(x,subst(e1),e2)
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Call(e1, e2)   => Call(subst(e1), subst(e2))
      case _ => throw new UnsupportedOperationException
    }
  }

  def step(e: Expr): Expr = {
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case e if isValue(e) => e

      //DoNeg
      //DoNot
      case Unary(op, e1) if isValue(e1) => op match {
        case Neg => N(-toNumber(e1))
        case Not => B(!toBoolean(e1))
      }
      //DoSeq
      case Binary(Seq,e1,e2) if isValue(e1) => e2

      //DoAnd
      case Binary(And,e1,e2) if isValue(e1) => if (toBoolean(e1)) e2 else e1
      //DoOr
      case Binary(Or, e1,e2) if isValue(e1) => if (toBoolean(e1)) e1 else e2

      //DoIf
      case If(e1,e2,e3) if (isValue(e1)) => if (toBoolean(e1)) e2 else e3
      //DoConst
      case ConstDecl(x,e1, e2) if (isValue(e1)) => substitute(e2, e1, x)

      case Binary(bop, v1, v2) if (isValue(v1) && isValue(v2)) => (bop: @unchecked) match {
        // DoPlus
        case Plus => (v1, v2) match {
          case (S(s1), S(s2)) => S(s1 + s2)
          case (S(s1),_) => S(s1 + toStr(v2))
          case (_,S(s2)) => S(toStr(v1) + s2)
          case (_,_) => N(toNumber(v1) + toNumber(v2))
        }
        // DoArith
        case Minus => N(toNumber(v1) - toNumber(v2))
        case Times => N(toNumber(v1) * toNumber(v2))
        case Div   => N(toNumber(v1) / toNumber(v2))

        // DoInequality
        case Lt|Le|Gt|Ge => B(inequalityVal(bop, v1, v2))

        // DoEquality
        case Eq|Ne => (v1,v2) match {
          case (Function(_,_,_),_) => throw new DynamicTypeError(v1)
          case (_,Function(_,_,_)) => throw new DynamicTypeError(v2)
          case _ => B(isEqual(v1,v2))
        }
      }

      // DoCall
      case Call(v1,v2) if (isValue(v1) && isValue(v2)) => v1 match {
        case Function(Some(fname),x,e) => substitute(substitute(e,v1,fname),v2,x)
        case Function(None,x,e) => substitute(e,v2,x)
        case _ => throw new DynamicTypeError(v1)
      }

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))

      // ****** Your cases here
      // Search
      case Unary(op, e1) if(!isValue(e1)) => Unary(op, step(e1))
      case Binary(op, v1, e2) if (isValue(v1)) => (op, v1, e2) match {
        case (Eq, v1, Function(_, _, _)) => throw new DynamicTypeError(e)
        case (Eq, Function(_, _, _), e2) => throw new DynamicTypeError(e)
        case (Ne, v1, Function(_, _, _)) => throw new DynamicTypeError(e)
        case (Ne, Function(_, _, _), e2) => throw new DynamicTypeError(e)
        case (_, _, _) => Binary(op, v1, step(e2))
      }
      case Binary(op, e1, e2) if (!isValue(e1)) => Binary(op, step(e1), e2)
      case Binary(bop, e1, e2) => Binary(bop,step(e1),e2)
      case If(e1, e2, e3) => If(step(e1),e2,e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x,step(e1),e2)
      case Call(v1, e2) if (isValue(v1)) => Call(v1, step(e2))
      case Call(e1, e2) => Call(step(e1), e2)

      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
    }
  }


  /* External Interfaces */

  //  this.debug = true // comment this out or set to false if you don't want print debugging information

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
  def evaluate(s: String): Expr = evaluate(jsy.lab3.Parser.parse(s))

  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging.
  def iterateStep(e: Expr): Expr = {
    require(closed(e))
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (n > 100) throw new RuntimeException("too many steps...")
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
  def iterateStep(s: String): Expr = iterateStep(jsy.lab3.Parser.parse(s))

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }

    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab3.Parser.parseFile(file)
      }} getOrElse {
        return
      }

    handle() {
      val v = evaluate(expr)
      println(pretty(v))
    }

    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }

}