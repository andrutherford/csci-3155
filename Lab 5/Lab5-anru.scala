package jsy.student

object Lab5 extends jsy.util.JsyApplication {
  import jsy.lab5.ast._
  import jsy.lab5._
  import jsy.lab5.DoWith._

  /*
   * CSCI 3155: Lab 5
   * Andrew Rutherford
   *
   * Partner: Bryce Strickland
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

  /*** Exercise with DoWith ***/

  def fresh: DoWith[Int,String] = doget flatMap { i =>
    val xp = "x" + i
    doput(i + 1) map { _ => xp }
  }

  def rename(env: Map[String, String], e: Expr): DoWith[Int,Expr] = {
    def ren(e: Expr): DoWith[Int,Expr] = rename(env, e)
    e match {
      //should return expression with nothing changed.
      case N(_) => doreturn(e)
      case Binary(Plus, e1, e2) => {
        ren(e1) flatMap {
          e1p => ren(e2) map {
            e2p => Binary(Plus, e1p, e2p)
          }
        }
      }
      //should return the renamed variable based on the state
      case Var(x) => doreturn(Var(env(x)))
      //should rename variables based on state
      case Decl(MConst, x, e1, e2) =>
        fresh flatMap {
          xp => ren(e1) flatMap {
            e1p => rename(env + (x->xp),e2) map {
              e2p => Decl(MConst, xp, e1p, e2p)
            }
          }
        }
      /* For this exercise, no need to implement any more cases than the ones above.
       * Leave the following default case. */
      case _ => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  def rename(e: Expr): Expr = {
    val (_, r) = rename(Map.empty, e)(0)
    r
  }

  def rename(s: String): Expr = rename(Parser.parse(s))

  /*** Helper: mapFirst to DoWith ***/

  // Just like mapFirst from Lab 4 but uses a callback f that returns a DoWith in the Some case.
  def mapFirstWith[W,A](f: A => Option[DoWith[W,A]])(l: List[A]): DoWith[W,List[A]] = l match {
    case Nil => doreturn(Nil)
    case h :: t => f(h) match {
      case None => for (tp <- mapFirstWith(f)(t)) yield h :: tp
      case Some(withhp) => for (hp <- withhp) yield hp :: t
    }
  }

  /*** Casting ***/

  //Specify when type t1 can be cast to type t2
  //Implement judgement form tau1 -> tau2
  def castOk(t1: Typ, t2: Typ): Boolean = (t1, t2) match {
    case (TNull, TObj(_)) => true
    case (_, _) if (t1 == t2) => true
    case (TObj(fields1), TObj(fields2)) => {
      val check1 = fields2 forall {
        case (field_1, t_1) => fields1.get(field_1) match {
          case Some(t_2) => if (t_1 == t_2) true else false
          case None => true
        }
      }

      val check2 = fields1 forall {
        case (field_1, t_1) => fields2.get(field_1) match {
          case Some (t_2) => if (t_1 == t_2) true else false
          case None => true
        }
      }
      check1 || check2
    }
    /***** Cases for the extra credit. Do not attempt until the rest of the assignment is complete. */
    case (TInterface(tvar, t1p), _) => ???
    case (_, TInterface(tvar, t2p)) => ???
    /***** Otherwise, false. */
    case _ => false
  }

  /*** Type Inference ***/

  type TEnv = Map[String, (Mutability,Typ)]
  val emp: TEnv = Map()
  def get(env: TEnv, x: String): (Mutability,Typ) = env(x)
  def extend(env: TEnv, x: String, mt: (Mutability,Typ)): TEnv = env + (x -> mt)

  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }

  // A helper function to translate parameter passing mode to the mutability of
  // the variable.
  def mut(m: PMode): Mutability = m match {
    case PName => MConst
    case PVar | PRef => MVar
  }

  def typeInfer(env: TEnv, e: Expr): Typ = {
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) =>
        val (_, t) = env(x)
        t
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      /***** Cases directly from Lab 4. We will minimize the test of these cases in Lab 5. */
      case Unary(Not, e1) => typ(e1) match {
        case TBool => TBool
        case t => err(t, e1)
      }
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
        case _ => if (typ(e1) == typ(e2)) TBool else err(typ(e2), e2)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => typ(e1) match {
        case TNumber => if (typ(e2) == TNumber) TBool else err(typ(e2), e2)
        case TString => if (typ(e2) == TString) TBool else err(typ(e2), e2)
        case _ => err(typ(e1), e1)
      }
      case Binary(And|Or, e1, e2) => typ(e1) match {
        case TBool => if (typ(e2) == TBool) TBool else err(typ(e2), e2)
        case _ => err(typ(e1), e1)
      }
      case Binary(Seq, e1, e2) => typ(e1); typ(e2)

      case If(e1, e2, e3) =>(typ(e1), typ(e2), typ(e3)) match {
        case (TBool, t1, t2) => if (t1 == t2) t1 else err(t2, e3)
        case (tgot, _, _) => err(tgot, e1)
      }
      case Obj(fields) => TObj(fields.map { case (s, e) => (s, typ(e)) })
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

      /***** Cases from Lab 4 that need a small amount of adapting. */
      case Decl(mut, x, e1, e2) => typeInfer(env + (x->(mut,typ(e1))), e2)
      case Function(p, paramse, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(rt)) =>
            val tprime = TFunction(paramse, rt)
            env + (f -> (MConst, tprime))
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with the parameters.
        val env2 = paramse match {
          case Left(params) =>
            params.foldLeft(env1)( (accEnv,key) => {
              val (s,t) = key
              accEnv + (s -> (MConst,t))
            })
          case Right((mode,x,t)) => mode match {
            case PName       => env1 + (x -> (MConst,t))
            case PVar | PRef => env1 + (x -> (MVar,t))
          }

        }
        // Infer the type of the function body
        val t1 = typeInfer(env2, e1)
        tann foreach { rt => if (rt != t1) err(t1, e1) };
        TFunction(paramse, t1)
      }

      case Call(e1, args) => typ(e1) match {
        case TFunction(Left(params), tret) if (params.length == args.length) => {
          (params, args).zipped.foreach {


            case((x,t),x2) =>
              if (t != typ(x2)) err(t,x2)
          }
          tret
        }
        case tgot @ TFunction(Right((mode,_,tparam)), tret) if (args.length == 1) => {
          val targ0 = typ(args(0))
          mode match {
            case PName | PVar => if (targ0 != tparam) err(targ0, args(0)) else tret
            case PRef if isLExpr (args(0)) => if(targ0 != tparam) err(targ0, args(0)) else tret
            case _ => err(tgot, e)
          }
        }
        case tgot => err(tgot, e)
      }

      /***** New cases for Lab 5. ***/
      case Assign(Var(x), e1) => env.get(x) match {
        case Some((MVar, typ2)) if (typ(e1) == typ2) => typ2
        case _ => err(typ(e1), e1)
      }

      case Assign(GetField(e1, f), e2)  => typ(e1) match {
        case TObj(tfields) if (tfields.contains(f)) => {
          val t2 = typ(e2)
          if (tfields(f) == t2) {
            t2
          } else {
            err(t2, e2)
          }
        }
        case tgot => err(tgot, e1)
      }
      case Assign(_, _) => err(TUndefined, e)
      /*** If neither assign case is hit throw static type error on e1 ***/
      //case Assign(e1, e2) => err(typ(e1), e1)

      case Null => TNull

      case Unary(Cast(t1), e1) => typ(e1) match {
        case tgot if (castOk(tgot, t1))  => t1
        case tgot => err(tgot, e1)
      }


      /* Should not match: non-source expressions or should have been removed */
      case A(_) | Unary(Deref, _) | InterfaceDecl(_, _, _) => throw new IllegalArgumentException("Gremlins: Encountered unexpected expression %s.".format(e))
    }
  }

  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3 and Lab 4.
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

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    /* We removed the requirement that esub is a value to support call-by-name. */
    //require(isValue(esub), "Expr to substitute is not a value")
    /* We suggest that you add support for call-by-name last. */
    def subst(e: Expr): Expr = substitute(e, esub, x)
    val ep: Expr = avoidCapture(freeVars(esub), e)
    ep match {
      case N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
      case Print(e1) => Print(subst(e1))
      /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
      /***** Cases need a small adaption from Lab 3 */
      case Decl(mut, y, e1, e2) => Decl(mut, y, subst(e1), if (x ==  y) e2 else subst(e2))
      /***** Cases needing adapting from Lab 4 */
      case Function(p, paramse, retty, e1) =>
        val matchesArg = paramse match {
          case Left(params) => params.foldLeft(false)((a,b) => (b._1 == x) || a)
          case Right((_,name,_)) => x == name
        }
        val matchesFunName = p match {
          case None => false
          case Some(f) => f == x
        }
        if (matchesArg || matchesFunName) Function(p,paramse,retty,e1)
        else Function(p,paramse,retty,subst(e1))
      /***** Cases directly from Lab 4 */
      case Call(e1, args) => Call(subst(e1), args map (v1 => subst(v1)))
      case Obj(fields) => Obj(fields map { case (fi, ei) => (fi, subst(ei))})
      case GetField(e1, f) => GetField(subst(e1), f)

      /***** New case for Lab 5 */
      case Assign(e1, e2) => Assign(subst(e1), subst(e2))
      /***** Extra credit case for Lab 5 */
      //case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, subst(e1))
      case _ => e
    }
  }

  /* A small-step transition. */
  def step(e: Expr): DoWith[Mem, Expr] = {
    require(!isValue(e), "stepping on a value: %s".format(e))

    /*** Helpers for Call ***/

    def stepIfNotValue(e: Expr): Option[DoWith[Mem,Expr]] = if (isValue(e)) None else Some(step(e))

    /* Check whether or not the argument expression is ready to be applied. */
    def argApplyable(mode: PMode, arg: Expr): Boolean = mode match {
      case PVar => isValue(arg)
      case PName => true
      case PRef => isLValue(arg)
    }

    /*** Body ***/
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => doget map { m => println(pretty(m, v1)); Undefined }
      /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Unary(Neg, N(n1)) => doreturn( N(- n1) )
      case Unary(Not, B(b1)) => doreturn( B(! b1) )
      //case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Seq, v1, e2) if isValue(v1) => doreturn( e2 )
      case Binary(Plus, S(s1), S(s2)) => doreturn( S(s1 + s2) )
      case Binary(Plus, N(n1), N(n2)) => doreturn( N(n1 + n2) )
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(inequalityVal(bop, v1, v2)) )
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 == v2) )
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => doreturn( B(v1 != v2) )
      case Binary(And, B(b1), e2) => doreturn( if (b1) e2 else B(false) )
      case Binary(Or, B(b1), e2) => doreturn( if (b1) B(true) else e2 )
      case Binary(Minus, N(n1), N(n2)) => doreturn( N(n1 - n2) )
      case Binary(Times, N(n1), N(n2)) => doreturn( N(n1 * n2) )
      case Binary(Div, N(n1), N(n2)) => doreturn( N(n1 / n2) )
      case If(B(b1), e2, e3) => doreturn( if (b1) e2 else e3 )
      //case _ => ???
      /***** Cases needing adapting from Lab 4. Make sure to replace the case _ => ???. */
      case Obj(fields) if fields forall { case (_, vi) => isValue(vi)} => {
        memalloc(Obj(fields)) map { (a:A) => a:Expr}
      }
      case GetField(a @ A(_), f) => {
        doget.map {
          (m: Mem) => m.get(a) match {
            case Some(Obj(fields)) => fields.get(f) match {
              case Some(field) => field
              case _ => throw StuckError(e)
            }
            case _ => throw StuckError(e)
          }
        }
      }


      case Call(v1, args) if isValue(v1) =>
        def substfun(e1: Expr, p: Option[String]): Expr = p match {
          case None => e1
          case Some(x) => substitute(e1, v1, x)
        }
        (v1, args) match {
          /*** Fill-in the DoCall cases, the SearchCall2, the SearchCallVar, the SearchCallRef  ***/
          // DoCall / DoCallRec
          case (Function(p,Left(params),tann,e1),args) if (args forall isValue) =>
            if (params.length != args.length) throw StuckError(e);
            val e1p = (params,args).zipped.foldRight(e1) { case (((p,_),a),acc) => substitute(acc,a,p) }
            doreturn(substfun(e1p, p))

          // DoCallName / DoCallRecName
          case (Function(p,Right((PName,x1,typ)),tann,e1),e2 :: Nil) =>
            doreturn(substfun(substitute(e1,e2,x1),p))

          // DoCallVar / DoCallRecVar
          case (Function(p,Right((PVar,x1,typ)),tann,e1),v2 :: Nil) if isValue(v2) =>
            for (a <- memalloc(v2)) yield substfun(substitute(e1,Unary(Deref,a),x1),p)

          // DoCallRef / DoCallRecRef
          case (Function(p,Right((PRef,x1,typ)),tann,e1),lv2 :: Nil) if isLValue(lv2) =>
            doreturn(substfun(substitute(e1,lv2,x1),p))

          // SearchCall2
          case (Function(_,Left(_),_,_),args) =>
            for (argsp <- mapFirstWith(stepIfNotValue)(args)) yield Call(v1,argsp)

          // SearchCallVar
          case (Function(_,Right((PVar,_,_)),_,_),e2 :: Nil) =>
            for (e2p <- step(e2)) yield Call(v1,List(e2p))

          // SearchCallRef
          case (Function(_,Right((PRef,_,_)),_,_),e2 :: Nil) if (!isLValue(e2)) =>
            for (e2p <- step(e2)) yield Call(v1,List(e2p))

          case _ => throw StuckError(e)
        }

      case Decl(MConst, x, v1, e2) if isValue(v1) => {
        doreturn(substitute(e2, v1, x))
      }
      /*case Decl(MVar, x, v1, e2) if isValue(v1) => {
        memalloc(v1) map {
          a => substitute(e2, Unary(Deref, a), x)
        }
      }*/
      case Decl(MVar, x, v1, e2) if isValue(v1) =>
        for (a <- memalloc(v1)) yield substitute(e2,Unary(Deref,a),x)

      /***** New cases for Lab 5. */
      /*case Unary(Deref,a @ A(_)) => doget.map{
        w => w.get(a) match {
          case Some(e) => e
          case None => throw StuckError(e)
        }
      }*/
      case Unary(Deref, a @ A(_)) => {
        doget.map {
          (m: Mem) => m.apply(a)
        }
      }

      case Unary(Cast(t), Null) => doreturn(Null)
      case Unary(Cast(t), e1) => doreturn(e1)

      case Assign(Unary(Deref, a @ A(_)), v) if isValue(v) =>
        for (_ <- domodify { (m: Mem) =>
          if (!m.contains(a)) throw new StuckError(e)
          m + (a,v)
        }) yield v

      /*case Assign(GetField(a @ A(_), f), v) if isValue(v) =>  domodify({ (m: Mem) =>
        val newObj = m.get(a) match {
          case Some(Obj(fields)) => Obj(fields + (f -> v))
          case _ => throw StuckError(e)
        }
        m + (a -> newObj)
      }).map{_ => v}*/
      case Assign(GetField(a @ A(_),f), vp) if isValue(vp) =>
        for (_ <- domodify { (m: Mem) => m.get(a) match {
          case Some(Obj(fields)) if fields.contains(f) =>
            m + (a,Obj(fields + (f -> vp)))
          case _ => throw new StuckError(e)
        }
        }) yield vp

      /* Base Cases: Error Rules */
      /***** Replace the following case with a case to throw NullDeferenceError.  */
      //case _ => throw NullDeferenceError(e)

      /* Inductive Cases: Search Rules */
      /***** Cases needing adapting from Lab 3. Make sure to replace the case _ => ???. */
      case Print(e1) => step(e1) map { e1p => Print(e1p) }
      case Unary(uop, e1) =>
        for (e1p <- step(e1)) yield Unary(uop, e1p)
      //case Unary(uop, e1) => step(e1) map { e1p => Unary(uop, e1p)}
      case Binary(bop, e1, e2) if (isValue(e1)) => step(e2) map { e2p => Binary(bop, e1, e2p)}
      case Binary(bop, e1, e2) =>  step(e1) map { e1p => Binary(bop, e1p, e2)}
      case If(e1, e2, e3) => step(e1) map { e1p => If(e1p, e2, e3)}
      case GetField(Null,_) | Assign(GetField(Null,_),_) => throw new NullDereferenceError(e)
      /*case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
        case Some((fi,ei)) => {
          step(ei) map (r => Obj(fields + (fi -> r)))
        }
        case None => throw StuckError(e)
      }*/
      case Obj(fields) => fields find { case (_, ei) => !isValue(ei) } match {
        case Some((fi,ei)) => {
          for (eip <- step(ei)) yield Obj(fields + (fi -> eip))
        }
        case None => throw StuckError(e)
      }
      case GetField(e1, f) => {
        if (e1 == Null) throw new NullDereferenceError(e)
        for (e1p <- step(e1)) yield GetField(e1p, f)
      }

      /*** Fill-in more Search cases here. ***/
      /*** search Decl ***/
      //case Decl(mut, x, e1, e2) => step(e1) map (r => Decl(mut, x, r, e2))
      case Decl(mod, x, e1, e2) =>
        for (e1p <- step(e1)) yield Decl(mod, x, e1p, e2)
      /*** search Call ***/
      //case Call(e1, e2) => step(e1) map (ep => Call(ep, e2))
      case Call(e1,args) =>
        for (e1p <- step(e1)) yield Call(e1p, args)
      //Search assign
      /*case Assign(e1,e2) => {
        //Search assign 2
        if (isLValue(e1))
          if (isValue(e2)) throw StuckError(e) else step(e2) map (r => Assign(e1,r))
        //Search assign 1
        else
        if (isValue(e1)) throw StuckError(e) else step(e1) map (r => Assign(r,e2))
      }*/
      case Assign(e1, e2) if isLValue(e1) && !isValue(e2)=> {
        for (e2p <- step(e2)) yield Assign(e1, e2p)
      }
      case Assign(e1, e2) => {
        for (e1p <- step(e1)) yield Assign(e1p, e2)
      }
      /* Everything else is a stuck error. */
      case _ => throw StuckError(e)
    }
  }

  /*** Extra Credit: Lowering: Remove Interface Declarations ***/

  def removeInterfaceDecl(e: Expr): Expr =
  /* Do nothing by default. Change to attempt extra credit. */
    e

  /*** External Interfaces ***/

  //this.debug = true // comment this out or set to false if you don't want print debugging information
  //this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.

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

  case class TerminationError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }

  def iterateStep(e: Expr): Expr = {
    require(closed(e), "input Expr to iterateStep is not closed: free variables: %s".format(freeVars(e)) )
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

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(removeInterfaceDecl(jsy.lab5.Parser.parse(s)))

  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file

  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }

    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab5.Parser.parseFile(file)
      }} getOrElse {
        return
      }

    val exprlowered =
      handle(None: Option[Expr]) {Some{
        removeInterfaceDecl(expr)
      }} getOrElse {
        return
      }

    val welltyped = handle(false) {
      println("# Type checking ...")
      val t = inferType(exprlowered)
      println("## " + pretty(t))
      true
    }
    if (!welltyped) return

    handle() {
      println("# Stepping ...")
      def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
        if (Some(n) == maxSteps) throw TerminationError(e)
        else if (isValue(e)) doreturn( e )
        else {
          for {
            m <- doget[Mem]
            _ = println("## %4d:%n##  %s%n##  %s".format(n, m, e))
            ep <- step(e)
            epp <- loop(ep, n + 1)
          } yield
          epp
        }
      val (m,v) = loop(exprlowered, 0)(memempty)
      println("## %s%n%s".format(m,pretty(v)))
    }
  }

}