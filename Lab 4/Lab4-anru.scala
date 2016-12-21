package jsy.student

object Lab4 extends jsy.util.JsyApplication {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
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
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */

  //Eliminate consecutive duplicates of an element
  def compressRec[A](l: List[A]): List[A] = l match {
    //list is nil or begins with _, ends with nil
    case Nil | _ :: Nil => l
    //list begins with h1, next element is h2
    //t1 is the list beginning with h2 and ending with _
    case h1 :: (t1 @ (h2 :: _)) => {
      //If first element h1 matches second element h2, return remainder of the list without h1
      //Else join h1 with list and return
      if (h1 == h2) compressRec(t1) else h1 :: compressRec(t1)
    }
  }

  //Same as compressRec except recurse backwards from the right
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    //First iteration, acc is empty and h is the last element in the list
    (h, acc) =>
      acc match {
        case h1 :: _ => if (h == h1) acc else h :: acc
        //If empty or one element return
        case Nil | _ :: Nil => h :: acc
      }
  }

  //Find first element in l which when f applied to it returns some(x)
  def mapFirst[A](f: A => Option[A])(l: List[A]): List[A] = l match {
    //Return if list is nil
    case Nil => l
    //For a h::t list, apply function to head of the list and pattern match
    case h :: t => f(h) match {
      //If some(x) return the new list
      case Some(x) => x :: t
      //If not, look at second element
      case None => h :: mapFirst(f)(t)
    }
  }
  
  /* Search Trees */
  
  sealed abstract class Tree {
    def insert(n: Int): Tree = this match {
      case Empty => Node(Empty, n, Empty)
      case Node(l, d, r) => if (n < d) Node(l insert n, d, r) else Node(l, d, r insert n)
    } 

    //Perform in-order traversal of tree 'this' calling the callback f to accumulate result
    def foldLeft[A](z: A)(f: (A, Int) => A): A = {
      def loop(acc: A, t: Tree): A = t match {
        //If the node is a leaf return acc
        case Empty => acc
        case Node(l, d, r) => {
          //Recurse to the left
          var left = loop(acc, l)
          //Apply function to the center
          var data = f(left, d)
          //Recurse to the right
          loop(data, r)
        }
      }
      loop(z, this)
    }
    
    def pretty: String = {
      def p(acc: String, t: Tree, indent: Int): String = t match {
        case Empty => acc
        case Node(l, d, r) =>
          val spacer = " " * indent
          p("%s%d%n".format(spacer, d) + p(acc, l, indent + 2), r, indent + 2)
      } 
      p("", this, 0)
    }
  }
  case object Empty extends Tree
  case class Node(l: Tree, d: Int, r: Tree) extends Tree
  
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
  def sum(t: Tree): Int = t.foldLeft(0){ (acc, d) => acc + d }

  //Check that the data values of t as an in-order traversal are in strictly ascending order
  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = t.foldLeft((true, None: Option[Int])){
      (acc, d) => acc match {
        case (b1, None) => (b1, Some(d))
        case (b2, nextInt) => (nextInt.get < d && b2, Some(d))

      }
    }
    b
  }
  

  /* Type Inference */

  type TEnv = Map[String, Typ]
  val emp: TEnv = Map()
  def get(env: TEnv, x: String): Typ = env(x)
  def extend(env: TEnv, x: String, t: Typ): TEnv = env + (x -> t)
  
  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeInfer(env: TEnv, e: Expr): Typ = {
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case S(_) => TString
      case Undefined => TUndefined
      case Var(x) => env(x)
      case ConstDecl(x, e1, e2) => typeInfer(extend(env, x, typ(e1)), e2)
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case t => err(t, e1)
      }
      /*case Binary(Plus, e1, e2) => (typ(e1),typ(e2)) match {
        //TYPEARITH
        case (TNumber, TNumber) => TNumber
        //TYPEPLUSSTRING
        case (TString, TString) => TString
        case _ => err(typ(e1), e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typ(e1), typ(e2)) match {
        //TYPEARITH
        case (TNumber, TNumber) => TNumber
        //TYPEPLUSSTRING
        case _ => err(typ(e1), e1)
      }
      */
      case Binary(Plus, e1, e2) => typ(e1) match {
        case TString => if (typ(e2) == TString) TString else err(typ(e2), e2)
        case TNumber => if (typ(e2) == TNumber) TNumber else err(typ(e2), e2)
        case _ => err(typ(e1), e1)
      }

      case Binary(Minus|Times|Div, e1, e2) => typ(e1) match {
        case TNumber => if (typ(e2) == TNumber) TNumber else err(typ(e2), e2)
        case _ => err(typ(e1), e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typ(e1), typ(e2)) match {
        case (TFunction(params, tret), _) => err(TFunction(params, tret), e1)
        case (_, TFunction(params, tret)) => err(TFunction(params, tret), e2)
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (TBool, TBool) => TBool
        case (TObj(o1), TObj(o2)) => TBool
        case (TUndefined, TUndefined) => TBool
        case _ => if (typ(e1) == typ(e2)) TBool else err(typ(e2), e2)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typ(e1)) match {
        case (TNumber) => if (typ(e1) == TNumber) TBool else err(typ(e2), e2)
        case (TString) => if (typ(e2) == TString) TBool else err(typ(e2), e2)
        case _ => err(typ(e1), e1)
      }
      case Binary(And|Or, e1, e2) => (typ(e1)) match {
        case TBool => if (typ(e2) == TBool) TBool else err(typ(e2), e2)
        case _ => err(typ(e1), e1)
      }
      case Binary(Seq, e1, e2) => typ(e1); typ(e2)

      case If(e1, e2, e3) => (typ(e1),typ(e2), typ(e3)) match {
        case (TBool, t1, t2) => if (t1 == t2) t1 else err(t2, e3)
        case (tgot, _, _) => err(tgot, e1)
      }

      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            env + (f -> tprime)
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        //foldleft takes an initial value env1, and has a function with an accumulator and a mapping from x1 to t1
        val env2 = params.foldLeft(env1)({ case (acc,(x1,t1)) => acc + (x1 -> t1) })
        // Match on whether the return type is specified.
        tann match {
          case None => {
            val t = typeInfer(env2, e1)
            val tprime = TFunction(params, t)
            tprime
          }
          case Some(tret) => {
            //Ensure tret is a valid type
            val t = typeInfer(env2, e1)
            //Compare type specification to returned type
            if (TFunction(params, tret) != TFunction(params, t)) err(TFunction(params, t), e1) else TFunction(params, t)
          }
        }
      }
      case Call(e1, args) => typ(e1) match {
        case TFunction(params, tret) if (params.length == args.length) => {
          val pairs = params zip args
          pairs.foreach {
            pair =>
              val (v1, v2) = pair
              if (v1._2 != typ(v2)) err(typ(v2), v2) else typ(v2)
          };
          tret
        }
        case tgot => err(tgot, e1)
      }


      //If we have an object s -> is set to type t
      case Obj(fields) => TObj(fields.map { case (s, e) => (s, typ(e)) })

      //What is the type of cat.name()
      //This is just like a unary operator
      case GetField(e1, f) => {
        val e = typ(e1)
        e match {
          case TObj(fields) => fields.get(f) match {
            case None => err(e, e1)
            case Some(v) => v
          }
          case _ => err(e, e1)
        }
      }
    }
  }
  
  
  /* Small-Step Interpreter */

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), "v1 in inequalityVal is not a value")
    require(isValue(v2), "v2 in inqualityVal is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 <= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }

  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v), "Expr to substitute is not a value")

    def subst(e: Expr): Expr = substitute(e, v, x)

    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      //Double check this
      case Var(y) => if (x == y) v else e
      case ConstDecl(y, e1, e2) => if (y == x) ConstDecl(y, subst(e1), e2) else ConstDecl(y, subst(e1), subst(e2))
      case Function(p, params, tann, e1) => {
        if (params.exists((t1: (String, Typ)) => t1._1 == x) || Some(x) == p) {
        //check names of each parameter to see if name matches with x, and return function
          e
        } else {
          //else recurce on a substituted body  part of the function
          Function(p, params, tann, subst(e1))
        }

      }
      case Call(e1, args) => Call(subst(e1), args map subst)
      //Recursively subst through entire tree
      case Obj(fields) => Obj(fields.mapValues((v => subst(v))))
      case GetField(e1, f) => GetField(subst(e1), f)
    }
  }

  def step(e: Expr): Expr = {
    require(!isValue(e), "input Expr to step is a value")

    def stepIfNotValue(e: Expr): Option[Expr] = if (isValue(e)) None else Some(step(e))

    e match {
      /* Base Cases: Do Rules */
      //DOPRINT
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      //DONEG
      case Unary(Neg, N(n1)) => N(-n1)
      //DONOT
      case Unary(Not, B(b1)) => B(!b1)
      //DOSEQ
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      //DOARITH
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times,N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)
      //DOPLUSSTRING
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      //DOINEQUALITYNUMBER
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))
      //DOEQUALITY
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)
      //DOANDTRUE DOANDFALSE
      case Binary(And, B(b1), e2) => if (b1) e2 else B(false)
      //DOORTRUE DOORFALSE
      case Binary(Or, B(b1), e2) => if (b1) B(true) else e2
      //DOCONST
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)

      //DOCALL
      case Call(v1, args) if isValue(v1) && (args forall isValue) =>
        v1 match {
          case Function(p, params, tann, e1) => {
            val e1p = (params, args).zipped.foldRight(e1){
              (paramAndBody:((String, Typ), Expr), body: Expr) => (paramAndBody, body) match {
                case (((str, typ), v1), body) => substitute(body, v1, str)
              }
            }
            p match {
              case None => e1p
              case Some(x1) => substitute(e1p, Function(Some(x1), params, tann, e1), x1)
            }
          }
          case _ => throw StuckError(e)
        }

      //DOGETFIELD
      case GetField(Obj(fields), f) => fields.get(f) match {
        case Some(e) => e
        case None => throw new StuckError(e)
      }
      /***** New cases for Lab 4. Make sure to replace the case _ => ???. */

      /* Inductive Cases: Search Rules */

      case Print(e1) => Print(step(e1))
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      case If(B(true), e2, e3) => e2
      case If(B(false), e2, e3) => e3
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)

      case Call(v1 @ Function(_, _, _, _), args) => {
        val args1 = mapFirst { (a: Expr) => if (!isValue(a)) Some(step(a)) else None } (args)
        Call(v1, args1)
      }
      case Call(e1, args) => Call(step(e1), args)
      case Obj(f) => {
        val fList = f.toList
        def newFunction(arg: (String, Expr)): Option[(String, Expr)] = {
          arg match {
            case (s, e1) => if (!isValue(e1)) Some(s, step(e1)) else None
          }
        }
        val newList = mapFirst(newFunction)(fList)
        val fMap = newList.toMap
        Obj(fMap)
      }

      //SEARHGETFIELD
      //THIS MUST GO LEFT TO RIGHT FOR COG (It is not deterministic but needs to be)
      case GetField(e1, f) => GetField(step(e1), f)

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => {
        println("$"+e+"$")
        throw StuckError(e)
      }

    }
  }
  
  
  /* External Interfaces */
  
  this.debug = true // uncomment this if you want to print debugging information

  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e), "input Expr to interateStep is not closed")
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

  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val e1 =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }

    val welltyped = handle(false) {
      println("# Type checking ...")
      val t = Lab4.inferType(e1)
      println(pretty(t))
      true
    }
    if (!welltyped) return

    handle() {
      println("# Stepping ...")
      def loop(e: Expr, n: Int): Expr = {
        println("## %4d: %s".format(n, e))
        if (isValue(e)) e else loop(Lab4.step(e), n + 1)
      }
      val v1 = loop(e1, 0)
      println(pretty(v1))
    }
  }

}

