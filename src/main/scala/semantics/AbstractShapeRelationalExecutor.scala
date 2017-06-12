package semantics

import semantics.domains.abstracting.SRMemory.{AMemory, AResult, AValue}
import semantics.domains.abstracting.ValueShape.ValueShape
import semantics.domains.abstracting._
import semantics.domains.common.Product._
import semantics.domains.common.{Flat, _}
import semantics.domains.concrete.{BasicValue, Value}
import syntax.{VarName, _}
import util.Counter

import scalaz.\/
import scalaz.syntax.either._
import scalaz.syntax.functor._

case class AbstractShapeRelationalExecutor(module: Module) {
  val Memory = SRMemoryOf(module)

  import Memory.ValueShape._
  import Memory._

  private
  val symbolCounter: Counter = Counter(0)

  private
  def genSymbol: Flat[VarName \/ RelCt] = FlatValue(s"sym$$${symbolCounter += 1}".left)

  private
  def updateStore(acstore : ACStore, varName: VarName, value: AValue): ACStore = {
    acstore.store match {
      case FlatValue(store) => ACStore(FlatValue(store.updated(varName, value)), acstore.path)
      case _ => acstore
    }
  }

  private
  def dropStoreVars(acstore : ACStore, varnames: Seq[VarName]): ACStore = {
    acstore.store match {
      case FlatValue(store) => ACStore(FlatValue(store -- varnames), acstore.path)
      case _ => acstore
    }
  }

  private
  def evalVar(acstore: ACStore, x: VarName): AMemories[AValue] = {
    acstore.store match {
      case FlatBot => Lattice[AMemories[AValue]].bot
      case FlatValue(store) =>
        if (store.contains(x)) AMemories[AValue](Set((SuccessResult(store(x)), acstore)))
        else AMemories[AValue](Set((ExceptionalResult(Error(UnassignedVarError(x))), acstore)))
      case FlatTop => AMemories[AValue](Set((SuccessResult(Lattice[AValue].top), acstore)))
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
          case SignBot => Set(SuccessResult((ValueShape.fromSign(SignBot), Lattice[Flat[VarName \/ RelCt]].bot)))
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

  def evalPlus(lsgn: Sign, rsgn: Sign): Set[AResult[Sign]] = {
    /*     \b  | -  | -0    | 0   | 0+    | +   | \t
    -------------------------------------------------
    \b   | \b  | \b | \b    | \b  | \b    | \b  | \b
    -    | \b  | -  | -     | -   | \t    | \t  | \t
    -0   | \b  | -  | -0    | -0  | \t    | \t  | \t
    0    | \b  | -  | -0    | 0   | 0+    | +   | \t
    0+   | \b  | \t | \t    | 0+  | 0+    | +   | \t
    +    | \b  | \t | \t    | +   | +     | +   | \t
    \t   | \b  | \t | \t    | \t  | \t    | \t  | \t
 */
    (lsgn, rsgn) match {
      case (_, SignBot) | (SignBot, _) => Set(SuccessResult(SignBot))
      case (_, SignTop) | (SignTop, _) |
           (Pos, Neg) | (Pos, NonPos) |
           (NonNeg, Neg) | (NonNeg, NonPos) |
           (Neg, NonNeg) | (NonPos, NonNeg) |
           (Neg, Pos) | (NonPos, Pos) => Set(SuccessResult(SignTop))
      case (NonPos, NonPos) | (Zero, NonPos) | (NonPos, Zero) => Set(SuccessResult(NonPos))
      case (NonNeg, NonNeg) | (Zero, NonNeg) | (NonNeg, Zero) => Set(SuccessResult(NonNeg))
      case (Zero, Zero) => Set(SuccessResult(Zero))
      case (Neg, Neg) | (Neg, NonPos) | (Neg, Zero) |
           (Zero, Neg) | (NonPos, Neg) => Set(SuccessResult(Neg))
      case (NonNeg, Pos) | (Pos, NonNeg) | (Pos, Pos) | (Pos, Zero) | (Zero, Pos) => Set(SuccessResult(Pos))
    }
  }

  private
  def getBool(vl: AValue): Set[AResult[(Boolean, RelCt)]] = {
    val (vls, relcmp) = vl
    if (ValueShape.isBot(vls) || relcmp == Lattice[Flat[VarName \/ RelCt]].bot) Set()
    else {
      val rr = relcmp match {
        case FlatBot => FalseCt
        case FlatValue(v) => v.fold(_ => TrueCt, identity) // Perhaps include relations over boolean vars as well
        case FlatTop => TrueCt
      }
      if (ValueShape.isTop(vls)) {
        Set(ExceptionalResult(Error(TypeError(vl, DataType("bool")))),
          SuccessResult((true, rr)), SuccessResult((false, rr)))
      } else {
        ValueShape.toDataShape(vls).fold(Set[AResult[(Boolean, RelCt)]](ExceptionalResult(Error(TypeError(vl, DataType("bool")))))) {
          case DataBot() => Set()
          case DataElements(typeName, consShape) if typeName == "bool" =>
            consShape.toList.map {
              case ("true", List()) => SuccessResult((true, rr))
              case ("false", List()) => SuccessResult((false, rr))
              case _ => throw NonNormalFormMemories
            }.toSet
          case DataAny(typeName) if typeName == "bool" =>
            Set(SuccessResult((true, rr)), SuccessResult((false, rr)))
          case DataTop() => Set(ExceptionalResult(Error(TypeError(vl, DataType("bool")))),
            SuccessResult((true, rr)), SuccessResult((false, rr)))
          case _ => Set(ExceptionalResult(Error(TypeError(vl, DataType("bool")))))
        }
      }
    }
  }

  def toBoolDataShape(b: Boolean): DataShape[ValueShape] = {
    if (b) DataElements("bool", Map("true" -> List()))
    else DataElements("bool", Map("false" -> List()))
  }



  // TODO Consider tracking relational constraints for Boolean variables or treating Boolean variables specifically
  private
  def evalBinaryOp(lhvl: AValue, op: OpName, rhvl: AValue, acstore: ACStore): AMemories[AValue] = {
    def evalBinBoolOp(bop: (Boolean, Boolean) => Boolean) = {
      Lattice[AMemories[AValue]].lub(getBool(lhvl).map {
        case SuccessResult((lhb, lhrelcmp)) =>
          Lattice[AMemories[AValue]].lub(getBool(rhvl).map {
            case SuccessResult((rhb, rhrelcmp)) =>
              AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(toBoolDataShape(bop(lhb, rhb))),
                FlatValue(AndCt(lhrelcmp, lhrelcmp).right))), acstore)))
            case ExceptionalResult(exres) => AMemories[AValue](Set((ExceptionalResult(exres), acstore)))
          })
        case ExceptionalResult(exres) => AMemories[AValue](Set((ExceptionalResult(exres), acstore)))
      })
    }
    op match {
      case "==" | "!=" =>
        def boolop(phi: RelCt, psi: RelCt) =
          if (op == "==") RelCt.biImplCt(phi, psi)
          else NotCt(RelCt.biImplCt(phi, psi))
        def opct(pathsorct: (DataPath[Nothing], DataPath[Nothing]) \/ Flat[RelCt]): Flat[VarName \/ RelCt] = {
          pathsorct.fold[Flat[VarName \/ RelCt]]({ case (ldp, rdp) => FlatValue(OpCt(ldp, op, rdp).right) }, _.map(_.right))
        }
        val trueres = (SuccessResult((ValueShape.fromDataShape(DataElements("bool", Map("true" -> List()))), FlatValue(TrueCt.right))), acstore)
        val falseres = (SuccessResult((ValueShape.fromDataShape(DataElements("bool", Map("false" -> List()))), FlatValue(TrueCt.right))), acstore)
        val defValue = if (op == "==") AMemories[AValue](Set(falseres))
                       else AMemories[AValue](Set(trueres))
        def getPaths(lhvrelcmp: Flat[VarName \/ RelCt], rhvrelcmp: Flat[VarName \/ RelCt]): (VarName, VarName) \/ Flat[RelCt] = {
          lhvrelcmp match {
            case FlatBot => FlatBot.right
            case FlatValue(lhrc) => rhvrelcmp match {
              case FlatBot => FlatBot.right
              case FlatValue(rhrc) =>
                lhrc.fold(lhsym =>
                  rhrc.fold(rhsym => (lhsym, rhsym).left,
                    rhrel => FlatValue(boolop(IsCt(DataPath(lhsym, List()), "true"), rhrel)).right),
                  lhrel =>
                    FlatValue(boolop(lhrel, rhrc.fold(rhsym => IsCt(DataPath(rhsym, List()), "true"), identity))).right)
              case FlatTop => FlatTop.right
            }
            case FlatTop => FlatTop.right
          }
        }
        def doSign(lhsign: Sign, rhsign: Sign,
                   pathsorct: (DataPath[Nothing], DataPath[Nothing]) \/ Flat[RelCt]): AMemories[AValue] =
          (lhsign, rhsign) match {
            case (SignBot, _) | (_, SignBot) => AMemories(Set())
            case (SignTop, _) | (_, SignTop) =>
              AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acstore)))
            case (Neg, Pos) | (Neg, NonNeg) |
                 (Pos, Neg) | (NonNeg, Neg) |
                 (Pos, NonPos) | (NonPos, Pos) |
                 (Zero, Neg) | (Neg, Zero) | (Pos, Zero) | (Zero, Pos) =>
              AMemories[AValue](Set(falseres))
            case (Zero, Zero) =>
              AMemories[AValue](Set(trueres))
            case (NonNeg, Pos) | (Pos, NonNeg) |
                 (NonPos, Neg) | (Neg, NonPos) |
                 (Pos, Pos) | (Neg, Neg) |
                 (NonPos, Zero) | (Zero, NonPos) |
                 (NonNeg, Zero) | (Zero, NonNeg) |
                 (NonNeg, NonNeg) | (NonPos, NonPos) |
                 (NonPos, NonNeg) | (NonNeg, NonPos) =>
              AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acstore)))
          }
        def doList(lhlistshape: ListShape[ValueShape], rhlistshape: ListShape[ValueShape],
                   pathsorct: (DataPath[Nothing], DataPath[Nothing]) \/ Flat[RelCt]): AMemories[AValue] =
          (lhlistshape, rhlistshape) match {
            case (ListBot(), _) | (_, ListBot()) => AMemories(Set())
            case (ListTop(), _) | (_, ListTop()) =>
              AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acstore)))
            case (ListElements(e1), ListElements(e2)) =>
              Lattice[AMemories[AValue]].lub(doValue(e1, e2, FlatValue(TrueCt).right).memories.map { case (ares, acs) =>
                  ares match {
                    case SuccessResult((vs, vrelcmp)) =>
                      if (Lattice[ValueShape].<=(ValueShape.fromDataShape(DataElements("bool", Map("true" -> List()))), vs)) {
                        AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acs)))
                      }
                      else AMemories[AValue](Set(falseres))
                    case ExceptionalResult(exres) => AMemories[AValue](Set((ExceptionalResult(exres), acs)))
                  }
              })
          }
        def doData(lhdatashape: DataShape[ValueShape], rhdatashape: DataShape[ValueShape],
                   pathsorct: (DataPath[Nothing], DataPath[Nothing]) \/ Flat[RelCt]): AMemories[AValue] = {
          // TODO Consider refining existing shapes/operands given result
          (lhdatashape, rhdatashape) match {
            case (DataBot(), _) | (_, DataBot()) => AMemories[AValue](Set())
            case (DataTop(), _) | (_, DataTop()) =>
              AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acstore)))
            case (DataAny(ty1), DataAny(ty2)) if ty1 == ty2 =>
              AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acstore)))
            case (DataAny(ty1), DataElements(ty2, elems2)) if ty1 == ty2 =>
              AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acstore)))
            case (DataElements(ty1, elems1), DataAny(ty2)) if ty1 == ty2 =>
              AMemories[AValue](Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acstore)))
            case (DataElements(ty1, elems1), DataElements(ty2, elems2)) if ty1 == ty2 =>
              val sharedConstructors = elems1.keySet intersect elems2.keySet
              val sharedsub = sharedConstructors.map { k =>
                val levs = elems1(k)
                val revs = elems2(k)
                val (_, pars) = module.constructors(k)
                val subcomp = levs.zip(revs).zip(pars).map { case ((lvs, rvs), par) =>
                  doValue(lvs, rvs, pathsorct.fold ({
                    case (ldp, rdp) =>
                      (DataPath(ldp.varName, ldp.accessPaths :+ FieldAccessPath(par.name)),
                        DataPath(rdp.varName, rdp.accessPaths :+ FieldAccessPath(par.name))).left
                  }, _ => FlatValue(TrueCt).right))
                }
                ??? // TODO Implement
              }
              if (sharedConstructors.nonEmpty) {
                ???
              } else {
                AMemories[AValue](Set(falseres))
              }
            case _ =>
              AMemories[AValue](Set(falseres))
          }
        }
        def doValue(lhvs: ValueShape, rhvs: ValueShape,
                    pathsorct: (DataPath[Nothing], DataPath[Nothing]) \/ Flat[RelCt]): AMemories[AValue] = {
          if (ValueShape.isBot(lhvs) || ValueShape.isBot(rhvs)) AMemories(Set())
          else if (ValueShape.isTop(lhvs) || ValueShape.isTop(rhvs)) {
            AMemories(Set((SuccessResult((ValueShape.fromDataShape(DataAny("bool")), opct(pathsorct))), acstore)))
          } else {
            ValueShape.toSign(lhvs).fold {
              ValueShape.toListShape(lhvs).fold {
                val lhdatashape = ValueShape.toDataShape(lhvs).get
                ValueShape.toDataShape(rhvs).fold(defValue) { rhdatashape => doData(lhdatashape, rhdatashape, pathsorct) }
              } { lhlistshape =>
                ValueShape.toListShape(rhvs).fold(defValue) { rhlistshape => doList(lhlistshape, rhlistshape, pathsorct) }
              }
            } { lhsign =>
              ValueShape.toSign(rhvs).fold(defValue) { rhsign => doSign(lhsign, rhsign, pathsorct) }
            }
          }
        }
        val (lhvs, lhvrelcmp) = lhvl
        val (rhvs, rhvrelcmp) = rhvl
        doValue(lhvs, rhvs, getPaths(lhvrelcmp, rhvrelcmp).fold({
          case (lhsym, rhsym) => (DataPath(lhsym, List()), DataPath(rhsym, List())).left }, _.right))
      case "in" => ???
      case "notin" => ???
      case "&&" =>
        evalBinBoolOp(_ && _)
      case "||" =>
        evalBinBoolOp(_ || _)
      case "+" =>
        AMemories(evalSignOp(lhvl, op, rhvl, (e1, e2) => evalPlus(e1, e2)).map((_, acstore)))
      case "-" =>
        // TODO Add lists, sets, other
        AMemories(evalSignOp(lhvl, op, rhvl, evalSubt).map((_, acstore)))
      case "*" =>
        AMemories(evalSignOp(lhvl, op, rhvl, evalMult).map((_, acstore)))
      case "/" =>
        AMemories(evalSignOp(lhvl, op, rhvl, evalDiv).map((_, acstore)))
      case "%" => ???
      case _ => AMemories(Set((ExceptionalResult(Error(InvalidOperationError(op, List(lhvl, rhvl)))), acstore)))
    }
  }

  private
  def evalSignOp(lhvl: AValue, op: OpName, rhvl: AValue,
                evalSign: (Sign, Sign) => Set[AResult[Sign]]) = {
    val (lhvs, lhrelcmp1) = lhvl
    val (rhvs, lhrelcmp2) = rhvl
    if (ValueShape.isBot(lhvs) || ValueShape.isBot(rhvs) ||
         lhrelcmp1 == Lattice[Flat[VarName \/ RelCt]].bot ||
          lhrelcmp2 == Lattice[Flat[VarName \/ RelCt]].bot) {
      Set[AResult[AValue]]()
    } else if (ValueShape.isTop(lhvs) && ValueShape.isTop(rhvs)) {
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
  def evalFor(localVars: Map[VarName, Type], acstore: ACStore, enum: Generator, body: Expr): AMemories[AValue] = ???

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
    case AssertExpr(cond) => evalAssert(localVars, acstore, cond)
  }

  def eval(acstore: ACStore, expr: Expr): AMemories[AValue] = evalLocal(Map.empty, acstore, expr)
}
