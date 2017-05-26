package semantics

import semantics.domains.abstracting.Memory.{AMemory, AResult, AValue}
import semantics.domains.abstracting.ValueShape.ValueShape
import semantics.domains.abstracting._
import semantics.domains.common._
import semantics.domains.common.Product._
import semantics.domains.concrete.{BasicValue, Value}
import semantics.domains.abstracting.Relational._
import syntax._
import semantics._
import util.Counter
import scalaz.syntax.functor._

import scalaz.\/

case class AbstractExecutor(module: Module) {
  val Memory = MemoryOf(module)

  import Memory.ValueShape._
  import Memory._

  private
  val symbolCounter: Counter = Counter(0)

  private
  def genSymbol: Flat[VarName] = FlatValue(s"sym$$${symbolCounter += 1}")

  private
  def updateStore(acstore : ACStore, varName: VarName, value: AValue): ACStore = {
    acstore.store match {
      case StoreTop => acstore
      case AbstractStore(store) => ACStore(AbstractStore(store.updated(varName, value)), acstore.path)
    }
  }

  private
  def dropStoreVars(acstore : ACStore, varnames: Seq[VarName]): ACStore = {
    acstore.store match {
      case StoreTop => acstore
      case AbstractStore(store) => ACStore(AbstractStore(store -- varnames), acstore.path)
    }
  }

  private
  def evalVar(acstore: ACStore, x: VarName): AMemories[AValue] = {
    acstore.store match {
      case StoreTop => AMemories[AValue](Set((SuccessResult(Lattice[AValue].top), acstore)))
      case AbstractStore(store) =>
        if (store.contains(x)) AMemories[AValue](Set((SuccessResult(store(x)), acstore)))
        else AMemories[AValue](Set((ExceptionalResult(Error(UnassignedVarError(x))), acstore)))
    }
  }

  private
  def evalUnaryOp(op: OpName, av: AValue): Set[AResult[AValue]] = {
    val (avs, sym1) = av
    op match {
      case "-" =>
        ValueShape.toSign(avs).fold[Set[AResult[AValue]]] {
          if(ValueShape.isTop(avs))
            Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))),
              SuccessResult((ValueShape.fromSign(SignTop), genSymbol)))
          else Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
        } {
          case SignBot => Set(SuccessResult((ValueShape.fromSign(SignBot), Lattice[Flat[VarName]].bot)))
          case Neg => Set(SuccessResult((ValueShape.fromSign(Pos), genSymbol)))
          case NonPos => Set(SuccessResult((ValueShape.fromSign(NonNeg), genSymbol)))
          case Zero => Set(SuccessResult((ValueShape.fromSign(Zero), genSymbol)))
          case NonNeg => Set(SuccessResult((ValueShape.fromSign(NonPos), genSymbol)))
          case Pos => Set(SuccessResult((ValueShape.fromSign(Pos), genSymbol)))
          case SignTop => Set(SuccessResult((ValueShape.fromSign(SignTop), genSymbol)))
        }
      case "!" =>
        ValueShape.toDataShape(avs).fold[Set[AResult[AValue]]] {
          if(ValueShape.isTop(avs))
            Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))),
              SuccessResult((ValueShape.fromDataShape(DataAny("Bool")), genSymbol)))
          else Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
        } {
          case DataBot() => Set(SuccessResult((ValueShape.fromDataShape(DataBot()), genSymbol)))
          case DataElements("Bool", consShape) =>
            Set(SuccessResult((ValueShape.fromDataShape(DataShape.dataElements("Bool", consShape.map {
              case ("true", List()) => ("false", List())
              case ("false", List()) => ("true", List())
              case _ => throw NonNormalFormMemories
            })), genSymbol)))
          case DataAny("Bool") =>
            Set(SuccessResult((ValueShape.fromDataShape(DataAny("Bool")), genSymbol)))
          case DataTop() =>
            Set(SuccessResult((ValueShape.fromDataShape(DataAny("Bool")), genSymbol)),
              ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
          case _ =>  Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
        }
      case _ => Set(ExceptionalResult(Error(InvalidOperationError(op, List(av)))))
    }
  }

  private
  def evalUnary(localVars: Map[VarName, Type], acstore: ACStore, operator: OpName, operand: Expr): AMemories[AValue] = {
    val mems = evalLocal(localVars, acstore, operand)
    Lattice[AMemories[AValue]].lub(mems.memories.map { case (res, acstore_) =>
      res match {
        case SuccessResult(avl) => AMemories[AValue](evalUnaryOp(operator, avl).map((_, acstore_)))
        case ExceptionalResult(exres) => AMemories[AValue](Set((ExceptionalResult(exres), acstore_)))
      }
    })
  }

  private
  def evalFieldAccess(localVars: Map[VarName, Type], acstore: ACStore, target: Expr, fieldName: FieldName): AMemories[AValue] = ???

  private
  def evalMult(lsgn: Sign, rsgn: Sign): Set[AResult[Sign]] = {
    /*         \b  | -  | -0 | 0  | 0+ | +  | \t
        -----------------------------------------
        \b   | \b  | \b | \b | \b | \b | \b | \b
        -    | \b  | +  | 0+ | 0  | -0 | -  | \t
        -0   | \b  | 0+ | 0+ | 0  | -0 | -0 | \t
        0    | \b  | 0  | 0  | 0  | 0  | 0  | 0
        0+   | \b  | -0 | -0 | 0  | 0+ | 0+ | \t
        +    | \b  | -  | -0 | 0  | 0+ | +  | \t
        \t   | \b  | \t | \t | 0  | \t | \t | \t
     */
    (lsgn, rsgn) match {
      case (SignBot, _) | (_, SignBot) => Set(SuccessResult(SignBot))
      case (Zero, _) | (_, Zero) => Set(SuccessResult(Zero))
      case (SignTop, _) | (_, SignTop) => Set(SuccessResult(SignTop))
      case (Pos, Pos) | (Neg, Neg) => Set(SuccessResult(Pos))
      case (Neg, Pos) | (Pos, Neg) => Set(SuccessResult(Neg))
      case (NonNeg, Pos) | (Pos, NonNeg) | (NonNeg, NonNeg) |
           (NonPos, Neg) | (Neg, NonPos) | (NonPos, NonPos) => Set(SuccessResult(NonNeg))
      case (Neg, NonNeg) | (NonNeg, Neg) | (NonNeg, NonPos) |
           (NonPos, NonNeg) | (Pos, NonPos) | (NonPos, Pos) => Set(SuccessResult(NonPos))
    }
  }

  def evalDiv (lhvl: Sign, rhvl: Sign): Set[AResult[Sign]] = {
    /*         \b  | -  | -0    | 0   | 0+    | +  | \t
        -----------------------------------------
        \b   | \b  | \b | \b    | ex  | \b    | \b | \b/ex
        -    | \b  | +  | +/ex  | ex  | -/ex  | -  | \t/ex
        -0   | \b  | 0+ | 0+/ex | ex  | -0/ex | -0 | \t/ex
        0    | \b  | 0  | 0/ex  | ex  | 0/ex  | 0  | 0/ex
        0+   | \b  | -0 | -0/ex | ex  | 0+/ex | 0+ | \t/ex
        +    | \b  | -  | -/ex  | ex  | +/ex  | +  | \t/ex
        \t   | \b  | \t | \t/ex | ex  | \t/ex | \t | \t/ex
     */
    (lhvl, rhvl) match {
      case (_, Zero) =>  Set(ExceptionalResult(Error(InvalidOperationError("/", List(lhvl, rhvl)))))
      case (SignBot, SignTop) =>
        Set(SuccessResult(SignBot), ExceptionalResult(Error(InvalidOperationError("/", List(lhvl, rhvl)))))
      case (SignBot, _) | (_, SignBot) => Set(SuccessResult(SignBot))
      case (Zero, SignTop) | (Zero, NonNeg) | (Zero, NonPos) =>
        Set(SuccessResult(Zero), ExceptionalResult(Error(InvalidOperationError("/", List(lhvl, rhvl)))))
      case  (Zero, Neg) | (Zero, Pos) =>
        Set(SuccessResult(Zero))
      case (_, SignTop) | (SignTop, NonPos) | (SignTop, NonNeg)  =>
        Set(SuccessResult(SignTop), ExceptionalResult(Error(InvalidOperationError("/", List(lhvl, rhvl)))))
      case (Neg, Pos) | (Pos, Neg) => Set(SuccessResult(Neg))
      case (Pos, Pos) | (Neg, Neg) => Set(SuccessResult(Pos))
      case (Neg, NonNeg) | (Pos, NonPos) =>
        Set(SuccessResult(Neg), ExceptionalResult(Error(InvalidOperationError("/", List(lhvl, rhvl)))))
      case (Neg, NonPos) | (Pos, NonNeg) =>
        Set(SuccessResult(Pos), ExceptionalResult(Error(InvalidOperationError("/", List(lhvl, rhvl)))))
      case (NonNeg, NonNeg) | (NonPos, NonPos) =>
        Set(SuccessResult(NonNeg), ExceptionalResult(Error(InvalidOperationError("/", List(lhvl, rhvl)))))
      case (NonNeg, NonPos) | (NonPos, NonNeg) =>
        Set(SuccessResult(NonPos), ExceptionalResult(Error(InvalidOperationError("/", List(lhvl, rhvl)))))
      case (NonNeg, Neg) | (NonPos, Pos) => Set(SuccessResult(NonPos))
      case (NonNeg, Pos) | (NonPos, Neg) => Set(SuccessResult(NonNeg))
      case (SignTop, _) => Set(SuccessResult(SignTop))
    }
  }

  def evalSubt(lsgn: Sign, rsgn: Sign): Set[AResult[Sign]] = {
    /*       \b  | -  | -0    | 0   | 0+    | +  | \t
      -----------------------------------------
      \b   | \b  | \b | \b    | \b  | \b    | \b | \b
      -    | \b  | \t | \t    | -   | -     | -  | \t
      -0   | \b  | \t | \t    | -0  | -0    | -  | \t
      0    | \b  | +  | 0+    | 0   | -0    | -  | \t
      0+   | \b  | +  | 0+    | 0+  | \t    | \t | \t
      +    | \b  | +  | +     | +   | \t    | \t | \t
      \t   | \b  | \t | \t    | \t  | \t    | \t | \t
   */
    (lsgn, rsgn) match {
      case (_, SignBot) | (SignBot, _) => Set(SuccessResult(SignBot))
      case (_, SignTop) | (SignTop, _) | (NonPos, Neg) | (NonPos, NonPos)
          | (Neg, Neg) | (Neg, NonPos) | (NonNeg, NonNeg) | (NonNeg, Pos)
          | (Pos, NonNeg) | (Pos, Pos) => Set(SuccessResult(SignTop))
      case (Neg, Zero) | (Neg, NonNeg) | (Neg, Pos) | (NonPos, Pos) | (Zero, Pos) => Set(SuccessResult(Neg))
      case (NonPos, Zero) | (NonPos, NonNeg) | (Zero, NonNeg) => Set(SuccessResult(NonPos))
      case (Zero, Zero) => Set(SuccessResult(Zero))
      case (NonNeg, Zero) | (NonNeg, NonPos) | (Zero, NonPos) => Set(SuccessResult(NonNeg))
      case (Pos, Zero) | (Pos, NonPos) | (Pos, Neg) | (NonNeg, Neg) | (Zero, Neg) => Set(SuccessResult(Pos))
    }
  }

  // TODO Consider tracking relational constraints for Boolean variables or treating Boolean variables specifically
  private
  def evalBinaryOp(lhvl: AValue, op: OpName, rhvl: AValue, acstore: ACStore): AMemories[AValue] = {
    val ress: Set[AResult[AValue]] = op match {
      case "==" => ???
      case "!=" => ???
      case "in" => ???
      case "notin" => ???
      case "&&" => ???
      case "||" => ???
      case "+" => ???
      case "-" =>
        evalSignOp(lhvl, op, rhvl, evalSubt)
      case "*" =>
        evalSignOp(lhvl, op, rhvl, evalMult)
      case "/" =>
        evalSignOp(lhvl, op, rhvl, evalDiv)
      case "%" => ???
      case _ => Set(ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl)))))
    }
    AMemories(ress.map(res => (res, acstore)))
  }

  private
  def evalSignOp(lhvl: (ValueShape, Flat[VarName]), op: OpName, rhvl: (ValueShape, Flat[VarName]),
                evalSign: (Sign, Sign) => Set[AResult[Sign]]) = {
    val (lhvs, lhsym) = lhvl
    val (rhvs, rhsym) = rhvl
    if (ValueShape.isTop(lhvs) && ValueShape.isTop(rhvs)) {
      Set(ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl))))) ++
        evalSign(SignTop, SignTop).map(_.map(sgnres => (ValueShape.fromSign(sgnres), genSymbol)))
    } else if (ValueShape.isTop(lhvs)) {
      Set(ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl))))) ++
        ValueShape.toSign(rhvs).fold(Set[AResult[AValue]]()) { rsgn =>
          evalSign(SignTop, rsgn).map(_.map(sgnres => (ValueShape.fromSign(sgnres), genSymbol)))
        }
    } else if (ValueShape.isTop(rhvs)) {
      Set(ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl))))) ++
        ValueShape.toSign(lhvs).fold(Set[AResult[AValue]]()) { lsgn =>
          evalSign(lsgn, SignTop).map(_.map(sgnres => (ValueShape.fromSign(sgnres), genSymbol)))
        }
    } else {
      ValueShape.toSign(lhvs).fold[Set[AResult[AValue]]](Set(ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl)))))) { lsgn =>
        ValueShape.toSign(rhvs).fold[Set[AResult[AValue]]](Set(ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl)))))) { rsgn =>
          evalSign(lsgn, rsgn).map(_.map(sgnres => (ValueShape.fromSign(sgnres), genSymbol)))
        }
      }
    }
  }

  private
  def evalBinaryHelper[E1 : Lattice, E2: Lattice](localVars: Map[VarName, Type], acstore: ACStore, left: Expr, op: OpName, right: Expr,
                          evalsub : (Map[VarName, Type], ACStore, Expr) => AMemories[E1], semop: (E1, OpName, E1, ACStore) => AMemories[E2]): AMemories[E2] = {
    val lhsmems = evalsub(localVars, acstore, left)
    Lattice[AMemories[E2]].lub(lhsmems.memories.map { case (lhres, acstore__) =>
        lhres match {
          case SuccessResult(lhval) =>
            val rhmems = evalsub(localVars, acstore__, right)
            Lattice[AMemories[E2]].lub(lhsmems.memories.map { case (rhres, acstore_) =>
                rhres match {
                  case SuccessResult(rhval) => semop(lhval, op, rhval, acstore_)
                  case ExceptionalResult(exres) => AMemories[E2](Set((ExceptionalResult(exres), acstore_)))
                }
            })
          case ExceptionalResult(exres) => AMemories[E2](Set((ExceptionalResult(exres), acstore__)))
        }
    })
  }

  private
  def evalBinaryRel(localVars: Map[VarName, Type], acstore: ACStore, left: Expr, op: OpName, right: Expr): AMemories[RelCt] = {
    op match {
      case "==" | "!=" | "in" | "notin" =>
        evalBinaryHelper[AValue, RelCt](localVars, acstore, left, op, right, evalLocal, ???)
      case "&&" | "||" =>
        evalBinaryHelper[RelCt, RelCt](localVars, acstore, left, op, right, evalAsRel, ???)
        // TODO Fix
      case _ => throw new RuntimeException(s"Unsupported binary rel: $left $op $right")
    }
  }

  private
  def evalAsRel(localVars: Map[VarName, Type], acstore: ACStore, expr: Expr): AMemories[RelCt] = expr match {
    case BinaryExpr(left, name, right) => evalBinaryRel(localVars, acstore, left, name, right)
      // TODO Consider more cases
    case _ => throw new RuntimeException(s"Can not evaluate $expr as a relation")
  }

  private
  def evalBinary(localVars: Map[VarName, Type], acstore: ACStore, left: Expr, op: OpName, right: Expr): AMemories[AValue] =
    evalBinaryHelper(localVars, acstore, left, op, right, evalLocal, evalBinaryOp)

  private
  def evalConstructor(localVars: Map[VarName, Type], acstore: ACStore, name: ConsName, args: Seq[Expr]): AMemories[AValue] = {
    val argsresmems = evalLocalAll(localVars, acstore, args)
    Lattice[AMemories[AValue]].lub(argsresmems.memories.map { case (argres, acstore_) =>
        argres match {
          case SuccessResult(vals) =>
            val (typ, parameters) = module.constructors(name)
            if (vals.length == parameters.length)
            // TODO Check types: vals.zip(parameters.map(_.typ)).forall((typing.checkType _).typed)
            // TODO Abstract relational constraints via paths
              AMemories(Set[AMemory[AValue]]((SuccessResult((fromDataShape(ValueShape.DataShape.dataElements(typ,
               Map(name -> vals.map(_._1)))), genSymbol)), acstore_)))
            else AMemories(Set[AMemory[AValue]]((ExceptionalResult(Error(SignatureMismatch(name, vals, parameters.map(_.typ)))), acstore_)))
          case ExceptionalResult(exres) => AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
        }
    })
  }

  private
  def evalList(localVars: Map[VarName, Type], acstore: ACStore, elements: Seq[Expr]): AMemories[AValue] = {
    val eresmems = evalLocalAll(localVars, acstore, elements)
    Lattice[AMemories[AValue]].lub(eresmems.memories.map { case (res, acstore_) =>
        res match {
          case SuccessResult(vals) =>
            AMemories(Set[AMemory[AValue]]((SuccessResult((fromListShape(ListShape.listElements(Lattice[ValueShape].lub(vals.map(_._1).toSet))),genSymbol)), acstore_)))
          case ExceptionalResult(exres) => AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
        }
    })
  }

  private
  def evalSet(localVars: Map[VarName, Type], acstore: ACStore, elements: Seq[Expr]): AMemories[AValue] = ???

  private
  def evalMap(localVars: Map[VarName, Type], acstore: ACStore, keyvalues: Seq[(Expr, Expr)]): AMemories[AValue] = ???

  private
  def evalMapLookup(localVars: Map[VarName, Type], acstore: ACStore, emap: Expr, ekey: Expr): AMemories[AValue] = ???

  private
  def evalMapUpdate(localVars: Map[VarName, Type], acstore: ACStore, emap: Expr, ekey: Expr, eval: Expr): AMemories[AValue] = ???

  private
  def evalFunCall(localVars: Map[VarName, Type], acstore: ACStore, functionName: VarName, args: Seq[Expr]): AMemories[AValue] = ???

  private
  def evalReturn(localVars: Map[VarName, Type], acstore: ACStore, result: Expr): AMemories[AValue] = {
    val resmems = evalLocal(localVars, acstore, result)
    Lattice[AMemories[AValue]].lub(resmems.memories.map { case (res, acstore_) =>
        res match {
          case SuccessResult(vl) =>
            AMemories(Set[AMemory[AValue]]((ExceptionalResult(Return(vl)), acstore_)))
          case ExceptionalResult(exres) =>
            AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
        }
    })
  }

  private
  def evalAssign(localVars: Map[VarName, Type], acstore: ACStore, assgn: Assignable, expr: Expr): AMemories[AValue] = ???

  private
  def evalIf(localVars: Map[VarName, Type], acstore: ACStore, cond: Expr, thenB: Expr, elseB: Expr): AMemories[AValue] = ???

  private
  def evalSwitch(localVars: Map[VarName, Type], acstore: ACStore, scrutinee: Expr, cases: Seq[Case]): AMemories[AValue] = ???


  private
  def evalVisit(localVars: Map[VarName, Type], acstore: ACStore, strategy: Strategy, scrutinee: Expr, cases: Seq[Case]): AMemories[AValue] = ???

  private
  def evalBlock(localVars: Map[VarName, Type], acstore: ACStore, vardefs: Seq[Parameter], exprs: Seq[Expr]): AMemories[AValue] = {
    val localVars_ = localVars ++ vardefs.map(par => par.name -> par.typ)
    val seqmems = evalLocalAll(localVars_, acstore, exprs)
    Lattice[AMemories[AValue]].lub(seqmems.memories.map { case (res, acstore__) =>
      val acstore_ = dropStoreVars(acstore__, vardefs.map(_.name))
      res match {
        case SuccessResult(vals) =>
          AMemories[AValue](Set((SuccessResult(vals.lastOption.getOrElse(Lattice[AValue].bot)), acstore_)))
        case ExceptionalResult(exres) => AMemories[AValue](Set((ExceptionalResult(exres), acstore_)))
      }
    })
  }

  private
  def evalFor(localVars: Map[VarName, Type], acstore: ACStore, enum: Enum, body: Expr): AMemories[AValue] = ???

  private
  def evalWhile(localVars: Map[VarName, Type], acstore: ACStore, cond: Expr, body: Expr): AMemories[AValue] = ???

  private
  def evalSolve(localVars: Map[VarName, Type], acstore: ACStore, vars: Seq[VarName], body: Expr): AMemories[AValue] = ???

  private
  def evalThrow(localVars: Map[VarName, Type], acstore: ACStore, result: Expr): AMemories[AValue] = {
    val resmems = evalLocal(localVars, acstore, result)
    Lattice[AMemories[AValue]].lub(resmems.memories.map { case (res, acstore_) =>
      res match {
        case SuccessResult(vl) =>
          AMemories(Set[AMemory[AValue]]((ExceptionalResult(Throw(vl)), acstore_)))
        case ExceptionalResult(exres) =>
          AMemories(Set[AMemory[AValue]]((ExceptionalResult(exres), acstore_)))
      }
    })
  }


  private
  def evalTryCatch(localVars: Map[VarName, Type], acstore: ACStore, tryB: Expr, catchVar: VarName, catchB: Expr): AMemories[AValue] = {
    val trymems = evalLocal(localVars, acstore, tryB)
    Lattice[AMemories[AValue]].lub(trymems.memories.map { case (tryres, acstore__) =>
        tryres match {
          case SuccessResult(tryval) => AMemories[AValue](Set((SuccessResult(tryval), acstore__)))
          case ExceptionalResult(exres) =>
            exres match {
              case Throw(value) =>
                val acstore_ = updateStore(acstore__, catchVar, value)
                evalLocal(localVars,acstore_, catchB)
              case _ => AMemories[AValue](Set((ExceptionalResult(exres), acstore__)))
            }
        }
    })
  }

  private
  def evalTryFinally(localVars: Map[VarName, Type], acstore: ACStore, tryB: Expr, finallyB: Expr): AMemories[AValue] = {
    val trymems = evalLocal(localVars, acstore, tryB)
    Lattice[AMemories[AValue]].lub(trymems.memories.map { case (tryres, acstore__) =>
      tryres match {
        case SuccessResult(vl) =>
          val finmems = evalLocal(localVars, acstore__, finallyB)
          Lattice[AMemories[AValue]].lub(finmems.memories.map { case (finres, acstore_) =>
            finres match {
              case SuccessResult(_) => AMemories[AValue](Set((SuccessResult(vl), acstore_)))
              case ExceptionalResult(exres) => AMemories[AValue](Set((ExceptionalResult(exres), acstore_)))
            }
          })
        case ExceptionalResult(exres) =>
          exres match {
            case Throw(_) =>
              val finmems = evalLocal(localVars, acstore__, finallyB)
              Lattice[AMemories[AValue]].lub(finmems.memories.map { case (finres, acstore_) =>
                  finres match {
                    case SuccessResult(_) =>
                      AMemories[AValue](Set((SuccessResult(Lattice[AValue].bot), acstore_)))
                    case ExceptionalResult(exres_) => AMemories[AValue](Set((ExceptionalResult(exres_), acstore_)))
                  }
              })
            case _ => AMemories[AValue](Set((ExceptionalResult(exres), acstore__)))
          }
      }
    })
  }

  private
  def evalEnumExpr(localVars: Map[VarName, Type], acstore: ACStore, enum: Enum): AMemories[AValue] = ???

  private
  def evalAssert(localVars: Map[VarName, Type], acstore: ACStore, cond: Expr): AMemories[AValue] = ???

  private
  def evalLocalAll(localVars: Map[VarName, Type], acstore: ACStore, exprs: Seq[Expr]): AMemories[List[AValue]] = {
    val amemories = exprs.toList.foldLeft[AMemories[List[AValue]]](AMemories(Set((SuccessResult(List()), acstore)))) { (prevmems, e) =>
      AMemories[List[AValue]](prevmems.memories.flatMap[AMemory[List[AValue]], Set[AMemory[List[AValue]]]] { case (prevres, acstore__) =>
          prevres match {
            case SuccessResult(vals) =>
              val newmems = evalLocal(localVars, acstore__, e)
              newmems.memories.map { case (res, acstore_) =>
                res match {
                  case SuccessResult(vl) =>
                    (SuccessResult(vals :+ vl), acstore_)
                  case ExceptionalResult(exres) => (ExceptionalResult(exres), acstore_)
                }
              }
            case ExceptionalResult(exres) => Set[AMemory[List[AValue]]]((ExceptionalResult(exres), acstore__))
          }
      })
    }
    amemories
  }

  private
  def evalLocal(localVars: Map[VarName, Type], acstore: ACStore, expr: Expr): AMemories[AValue] = expr match {
    case BasicExpr(b) =>
      AMemories[AValue](Set((SuccessResult((galois[Value, ValueShape].alpha(Set(BasicValue(b))), genSymbol)), acstore)))
    case VarExpr(name) => evalVar(acstore, name)
    case FieldAccExpr(target, fieldName) => evalFieldAccess(localVars, acstore, target, fieldName)
    case UnaryExpr(name, operand) => evalUnary(localVars, acstore, name, operand)
    case BinaryExpr(left, name, right) => evalBinary(localVars, acstore, left, name, right)
    case ConstructorExpr(name, args) => evalConstructor(localVars, acstore, name, args)
    case ListExpr(elements) => evalList(localVars, acstore, elements)
    case SetExpr(elements) => evalSet(localVars, acstore, elements)
    case MapExpr(keyvalues) => evalMap(localVars, acstore, keyvalues)
    case MapLookupExpr(emap, ekey) => evalMapLookup(localVars, acstore, emap, ekey)
    case MapUpdExpr(emap, ekey, eval) => evalMapUpdate(localVars, acstore, emap, ekey, eval)
    case FunCallExpr(functionName, args) => evalFunCall(localVars, acstore, functionName, args)
    case ReturnExpr(result) => evalReturn(localVars, acstore, result)
    case AssignExpr(assgn, targetexpr) => evalAssign(localVars, acstore, assgn, targetexpr)
    case IfExpr(cond, thenB, elseB) =>  evalIf(localVars, acstore, cond, thenB, elseB)
    case SwitchExpr(scrutinee, cases) =>  evalSwitch(localVars, acstore, scrutinee, cases)
    case VisitExpr(strategy, scrutinee, cases) => evalVisit(localVars, acstore, strategy, scrutinee, cases)
    case BreakExpr => AMemories[AValue](Set((ExceptionalResult(Break), acstore)))
    case ContinueExpr => AMemories[AValue](Set((ExceptionalResult(Continue), acstore)))
    case FailExpr => AMemories[AValue](Set((ExceptionalResult(Fail), acstore)))
    case LocalBlockExpr(vardefs, exprs) => evalBlock(localVars, acstore, vardefs, exprs)
    case ForExpr(enum, body) => evalFor(localVars, acstore, enum, body)
    case WhileExpr(cond, body) => evalWhile(localVars, acstore, cond, body)
    case SolveExpr(vars, body) => evalSolve(localVars, acstore, vars, body)
    case ThrowExpr(result) => evalThrow(localVars, acstore, result)
    case TryCatchExpr(tryB, catchVar, catchB) => evalTryCatch(localVars, acstore, tryB, catchVar, catchB)
    case TryFinallyExpr(tryB, finallyB) => evalTryFinally(localVars, acstore, tryB, finallyB)
    case EnumExpr(enum) => evalEnumExpr(localVars, acstore, enum)
    case AssertExpr(cond) => evalAssert(localVars, acstore, cond)
  }

  def eval(acstore: ACStore, expr: Expr): AMemories[AValue] = evalLocal(Map.empty, acstore, expr)
}
