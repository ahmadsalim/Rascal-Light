package semantics

import semantics.domains.abstracting.{TypeMemories, TypeMemory}
import semantics.domains.abstracting.TypeMemory.{TypeResult, TypeStore}
import semantics.domains.common._
import semantics.domains.concrete.TypeOps._
import TypeMemory._
import semantics.domains.concrete.ConstructorValue
import syntax._

case class AbstractTypeExecutor(module: Module) {
  private
  val typing = Typing(module)

  private
  def getVar(store: TypeStore, x: VarName): Option[(Boolean, Type)] = store match {
    case FlatBot => None
    case FlatValue(storemap) => storemap.get(x)
    case FlatTop => Some((true, Lattice[Type].top))
  }

  def evalVar(store: TypeStore, x: VarName): TypeMemories[Type] = {
    val unassignedError = Set(TypeMemory[Type](ExceptionalResult(Error(UnassignedVarError(x))), store))
    getVar(store, x).fold(TypeMemories(unassignedError)) {
      case (possUnassigned, typ) =>
        TypeMemories((if (possUnassigned) unassignedError else Set()) ++ Set(TypeMemory(SuccessResult(typ), store)))
    }
  }

  def accessField(tv: Type, fieldName: FieldName): Set[TypeResult[Type]] = tv match {
    case DataType(name) =>
      val conss = module.datatypes(name)
      val fieldTypes = conss.map(cons => module.constructors(cons)._2.find(_.name == fieldName).map(_.typ))
      val successres: Set[TypeResult[Type]] = Set(SuccessResult(Lattice[Type].lub(fieldTypes.flatten.toSet)))
      if (fieldTypes.forall(_.isDefined)) successres
      else Set(ExceptionalResult(Error(FieldError(tv, fieldName)))) ++ successres
    case ValueType =>
      val fieldTypUB =
        Lattice[Type].lub(module.constructors.values.toSet[(TypeName, List[Parameter])].map(_._2)
                                .flatMap(pars => pars.find(_.name == fieldName).map(_.typ))) // Take lub of all possible field types
      Set(ExceptionalResult(Error(FieldError(tv, fieldName)))) ++ Set(SuccessResult(fieldTypUB))
    case _ => Set(ExceptionalResult(Error(FieldError(tv, fieldName))))
  }

  def evalFieldAccess(localVars: Map[VarName, Type], store: TypeStore, target: Expr, fieldName: FieldName): TypeMemories[Type] = {
    val targetmems = evalLocal(localVars, store, target)
    Lattice[TypeMemories[Type]].lub(targetmems.memories.flatMap { case TypeMemory(targetres, store_) =>
      targetres match {
        case SuccessResult(tv) => accessField(tv, fieldName).map(res => TypeMemories[Type](Set(TypeMemory(res, store_))))
        case _ => Set(TypeMemories[Type](Set(TypeMemory(targetres, store_))))
      }
    })
  }

  def evalUnaryOp(op: OpName, vl: Type): Set[TypeResult[Type]] = (op, vl) match {
    case ("-", BaseType(IntType)) => Set(SuccessResult(BaseType(IntType)))
    case ("-", ValueType) =>
      Set(ExceptionalResult(Error(InvalidOperationError(op, List(vl))))) ++ Set(SuccessResult(BaseType(IntType)))
    case ("!", DataType("bool")) => Set(SuccessResult(DataType("bool")))
    case ("!", ValueType) =>
      Set(ExceptionalResult(Error(InvalidOperationError(op, List(vl))))) ++ Set(SuccessResult(DataType("bool")))
    case _ => Set(ExceptionalResult(Error(InvalidOperationError(op, List(vl)))))
  }

  def evalUnary(localVars: Map[VarName, Type], store: TypeStore, op: OpName, operand: Expr): TypeMemories[Type] = {
    val mems = evalLocal(localVars, store, operand)
    Lattice[TypeMemories[Type]].lub(mems.memories.flatMap { case TypeMemory(res, store_) =>
        res match {
          case SuccessResult(vl) =>
            evalUnaryOp(op, vl).map(res => TypeMemories(Set(TypeMemory(res, store_))))
          case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
        }
    })
  }

  def evalBinaryOp(lhtyp: Type, op: OpName, rhtyp: Type): Set[TypeResult[Type]] = {
    val invOp = ExceptionalResult(Error(InvalidOperationError(op, List(lhtyp, rhtyp))))
    (lhtyp, op, rhtyp) match {
      case (_, "==", _) => Set(SuccessResult(DataType("bool")))
      case (lhvl, "!=", rhvl) => Set(SuccessResult(DataType("bool")))
      case (lhvl, "in", ListType(ty)) => Set(SuccessResult(DataType("bool")))
      case (lhvl, "in", SetType(ty)) => Set(SuccessResult(DataType("bool")))
      case (lhvl, "in", MapType(kty, vty)) => Set(SuccessResult(DataType("bool")))
      case (lhvl, "in", ValueType) => Set(invOp, SuccessResult(DataType("bool")))
      case (lhvl, "notin", rhvl) => evalBinaryOp(lhvl, "in", rhvl).flatMap[TypeResult[Type], Set[TypeResult[Type]]] {
        case SuccessResult(ty) => evalUnaryOp("!", ty)
        case ExceptionalResult(exres) => Set(ExceptionalResult(exres))
      }
      case (DataType("bool"), "&&", DataType("bool")) =>
        Set(SuccessResult(DataType("bool")))
      case (ValueType | DataType("bool"), "&&", ValueType | DataType("bool")) =>
        Set(invOp, SuccessResult(DataType("bool")))
      case (DataType("bool"), "||", DataType("bool")) =>
        Set(SuccessResult(DataType("bool")))
      case (ValueType | DataType("bool"), "||", ValueType | DataType("bool")) =>
        Set(invOp, SuccessResult(DataType("bool")))
      case (BaseType(StringType), "+", BaseType(StringType)) =>
        Set(SuccessResult(BaseType(StringType)))
      case (BaseType(IntType), "+", BaseType(IntType)) =>
        Set(SuccessResult(BaseType(IntType)))
      case (BaseType(StringType), "+", ValueType) | (ValueType, "+", BaseType(StringType)) =>
        Set(invOp, SuccessResult(BaseType(StringType)))
      case (BaseType(IntType), "+", ValueType) | (ValueType, "+", BaseType(IntType)) =>
        Set(invOp, SuccessResult(BaseType(IntType)))
      case (ValueType, "+", ValueType) =>
        Set(invOp, SuccessResult(BaseType(StringType)), SuccessResult(BaseType(IntType)))
      case (BaseType(IntType), "-", BaseType(IntType)) =>
        Set(SuccessResult(BaseType(IntType)))
      case (ValueType | BaseType(IntType), "-", ValueType | BaseType(IntType)) =>
        Set(invOp, SuccessResult(BaseType(IntType)))
      case (BaseType(IntType), "*", BaseType(IntType)) =>
        Set(SuccessResult(BaseType(IntType)))
      case (ValueType | BaseType(IntType), "*", ValueType | BaseType(IntType)) =>
        Set(invOp, SuccessResult(BaseType(IntType)))
      case (BaseType(IntType), "/", BaseType(IntType)) =>
        Set(ExceptionalResult(Throw(DataType("divByZero"))), SuccessResult(BaseType(IntType)))
      case (ValueType | BaseType(IntType), "/", ValueType | BaseType(IntType)) =>
        Set(invOp, ExceptionalResult(Throw(DataType("divByZero"))), SuccessResult(BaseType(IntType)))
      case (BaseType(IntType), "%", BaseType(IntType)) =>
        Set(ExceptionalResult(Throw(DataType("modNonPos"))), SuccessResult(BaseType(IntType)))
      case (ValueType | BaseType(IntType), "%", ValueType | BaseType(IntType)) =>
        Set(invOp, ExceptionalResult(Throw(DataType("modNonPos"))), SuccessResult(BaseType(IntType)))
      case _ => Set(invOp)
    }
  }

  def evalBinary(localVars: Map[VarName, Type], store: TypeStore, left: Expr, op: OpName, right: Expr): TypeMemories[Type] = {
    val leftmems = evalLocal(localVars, store, left)
    Lattice[TypeMemories[Type]].lub(leftmems.memories.flatMap { case TypeMemory(lhres, store__) =>
        lhres match {
          case SuccessResult(lhval) =>
            val rightmems = evalLocal(localVars, store__, right)
            rightmems.memories.flatMap { case TypeMemory(rhres, store_) =>
                rhres match {
                  case SuccessResult(rhval) =>
                    evalBinaryOp(lhval, op, rhval).map(res => TypeMemories[Type](Set(TypeMemory(res, store_))))
                  case _ => Set(TypeMemories[Type](Set(TypeMemory(rhres, store_))))
                }
            }
          case _ => Set(TypeMemories[Type](Set(TypeMemory(lhres, store__))))
        }
    })
  }

  def evalConstructor(localVars: Map[VarName, Type], store: TypeStore, name: ConsName, args: Seq[Expr]): TypeMemories[Type] = {
    val argmems = evalLocalAll(localVars, store, args)
    Lattice[TypeMemories[Type]].lub(argmems.memories.flatMap {
      case TypeMemory(argres, store_) =>
        argres match {
          case SuccessResult(tys) =>
            val (tyname, parameters) = module.constructors(name)
            val tysparszipped = tys.zip(parameters.map(_.typ))
            val exRes: TypeMemory[Type] = TypeMemory(ExceptionalResult(Error(SignatureMismatch(name, tys, parameters.map(_.typ)))), store_)
            if (tys.length == parameters.length &&
                  tysparszipped.forall { case (ty1, ty2) => typing.isSubType(ty1, ty2) || ty1 == ValueType }) {
              val sucsRes: TypeMemory[Type] = TypeMemory(SuccessResult(DataType(tyname)), store_)
              if (tysparszipped.exists { case (ty1, ty2) => ty1 == ValueType && ty2 != ValueType })
                Set(TypeMemories(Set(exRes, sucsRes)))
              else Set(TypeMemories[Type](Set(sucsRes)))
            } else Set(TypeMemories[Type](Set(exRes)))
          case ExceptionalResult(exres) =>
            Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
        }
    })
  }

  def evalList(localVars: Map[VarName, Type], store: TypeStore, elements: Seq[Expr]): TypeMemories[Type] = {
    val elmems = evalLocalAll(localVars, store, elements)
    TypeMemories(elmems.memories.map[TypeMemory[Type], Set[TypeMemory[Type]]] { case TypeMemory(res, store_) =>
      res match {
        case SuccessResult(tys) => TypeMemory(SuccessResult(ListType(Lattice[Type].lub(tys.toSet[Type]))), store_)
        case ExceptionalResult(exres) => TypeMemory(ExceptionalResult(exres), store_)
      }
    })
  }

  def evalSet(localVars: Map[VarName, Type], store: TypeStore, elements: Seq[Expr]): TypeMemories[Type] = {
    val elmems = evalLocalAll(localVars, store, elements)
    TypeMemories(elmems.memories.map[TypeMemory[Type], Set[TypeMemory[Type]]] { case TypeMemory(res, store_) =>
      res match {
        case SuccessResult(tys) => TypeMemory(SuccessResult(SetType(Lattice[Type].lub(tys.toSet[Type]))), store_)
        case ExceptionalResult(exres) => TypeMemory(ExceptionalResult(exres), store_)
      }
    })
  }

  def evalMap(localVars: Map[VarName, Type], store: TypeStore, keyvalues: Seq[(Expr, Expr)]): TypeMemories[Type] = {
    val keymems = evalLocalAll(localVars, store, keyvalues.map(_._1))
    Lattice[TypeMemories[Type]].lub(keymems.memories.flatMap[TypeMemories[Type], Set[TypeMemories[Type]]] {
      case TypeMemory(keyres, store__) =>
        keyres match {
          case SuccessResult(keys) =>
            val valmems = evalLocalAll(localVars, store__, keyvalues.map(_._2))
            Set(TypeMemories(valmems.memories.map { case TypeMemory(valres, store_) =>
              valres match {
                case SuccessResult(vals) =>
                  TypeMemory[Type](SuccessResult(MapType(Lattice[Type].lub(keys.toSet), Lattice[Type].lub(vals.toSet))), store_)
                case ExceptionalResult(exres) =>
                  TypeMemory[Type](ExceptionalResult(exres), store_)
              }
            }))
          case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
        }
    })
  }

  def evalMapLookup(localVars: Map[VarName, Type], store: TypeStore, emap: Expr, ekey: Expr): TypeMemories[Type] = {
    val mapmems = evalLocal(localVars, store, emap)
    Lattice[TypeMemories[Type]].lub(mapmems.memories.flatMap { case TypeMemory(mapres, store__) =>
      mapres match {
        case SuccessResult(mapty) =>
          val exRes = TypeMemory[Type](ExceptionalResult(Error(TypeError(mapty, MapType(ValueType, ValueType)))), store__)
          def lookupOnMap(keyType: Type, valueType: Type) = {
            val keymems = evalLocal(localVars, store__, ekey)
            keymems.memories.flatMap[TypeMemories[Type], Set[TypeMemories[Type]]] { case TypeMemory(keyres, store_) =>
                keyres match {
                  case SuccessResult(actualKeyType) =>
                    if (actualKeyType == ValueType || typing.isSubType(actualKeyType, keyType)) {
                      val posEx = if (!typing.isSubType(actualKeyType, keyType))
                                       Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(Throw(DataType("nokey"))), store_))))
                                  else Set[TypeMemories[Type]]()
                      posEx ++ Set(TypeMemories[Type](Set(TypeMemory(SuccessResult(valueType), store_))))
                    }
                    else Set(TypeMemories(Set(TypeMemory(ExceptionalResult(Throw(DataType("nokey"))), store_))))
                  case ExceptionalResult(exres) =>
                    Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
                }
            }
          }
          mapty match {
            case MapType(keyType, valueType) => lookupOnMap(keyType, valueType)
            case ValueType => Set(TypeMemories(Set(exRes))) ++ lookupOnMap(ValueType, ValueType)
            case _ =>
              Set(TypeMemories[Type](Set(exRes)))
          }
        case ExceptionalResult(exres) =>
          Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
      }
    })
  }

  def evalMapUpdate(localVars: Map[VarName, Type], store: TypeStore, emap: Expr, ekey: Expr, evl: Expr): TypeMemories[Type] = {
    val mapmems = evalLocal(localVars, store, emap)
    Lattice[TypeMemories[Type]].lub(mapmems.memories.flatMap { case TypeMemory(mapres, store___) =>
      mapres match {
        case SuccessResult(mapt) =>
          def updateOnMap(keyType: Type, valueType: Type) = {
            val keymems = evalLocal(localVars, store___, ekey)
            keymems.memories.flatMap { case TypeMemory(keyres, store__) =>
              keyres match {
                case SuccessResult(keyt) =>
                  val valmems = evalLocal(localVars, store__, evl)
                  valmems.memories.flatMap { case TypeMemory(valres, store_) =>
                      valres match {
                        case SuccessResult(valt) =>
                          Set(TypeMemories[Type](
                            Set(TypeMemory(SuccessResult(MapType(Lattice[Type].lub(keyType, keyt),
                                                                 Lattice[Type].lub(valueType, valt))), store_))))
                        case ExceptionalResult(exres) =>
                          Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
                      }
                  }
                case ExceptionalResult(exres) =>
                  Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
              }
            }
          }
          val exRes = TypeMemory[Type](ExceptionalResult(Error(TypeError(mapt, MapType(ValueType, ValueType)))), store___)
          mapt match {
            case MapType(keyType, valueType) => updateOnMap(keyType, valueType)
            case ValueType => Set(TypeMemories(Set(exRes))) ++ updateOnMap(ValueType, ValueType)
            case _ => Set(TypeMemories(Set(exRes)))
          }
        case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store___))))
      }
    })
  }

  def evalFunCall(localVars: Map[VarName, Type], store: TypeStore, functionName: VarName, args: Seq[Expr]): TypeMemories[Type] = ???

  def evalReturn(localVars: Map[VarName, Type], store: TypeStore, evl: Expr): TypeMemories[Type] = ???

  def evalAssign(localVars: Map[VarName, Type], store: TypeStore, assgn: Assignable, targetexpr: Expr): TypeMemories[Type] = ???

  def evalIf(localVars: Map[VarName, Type], store: TypeStore, cond: Expr, thenB: Expr, elseB: Expr): TypeMemories[Type] = ???

  def evalSwitch(localVars: Map[VarName, Type], store: TypeStore, scrutinee: Expr, cases: Seq[Case]): TypeMemories[Type] = ???

  def evalVisit(localVars: Map[VarName, Type], store: TypeStore, strategy: Strategy, scrutinee: Expr, cases: Seq[Case]): TypeMemories[Type] = ???

  def evalBlock(localVars: Map[VarName, Type], store: TypeStore, vardefs: Seq[Parameter], exprs: Seq[Expr]): TypeMemories[Type] = ???

  def evalFor(localVars: Map[VarName, Type], store: TypeStore, enum: Enum, body: Expr): TypeMemories[Type] = ???

  def evalWhile(localVars: Map[VarName, Type], store: TypeStore, cond: Expr, body: Expr): TypeMemories[Type] = ???

  def evalSolve(localVars: Map[VarName, Type], store: TypeStore, vars: Seq[VarName], body: Expr): TypeMemories[Type] = ???

  def evalThrow(localVars: Map[VarName, Type], store: TypeStore, evl: Expr): TypeMemories[Type] = ???

  def evalTryCatch(localVars: Map[VarName, Type], store: TypeStore, tryB: Expr, catchVar: VarName, catchB: Expr): TypeMemories[Type] = ???

  def evalTryFinally(localVars: Map[VarName, Type], store: TypeStore, tryB: Expr, finallyB: Expr): TypeMemories[Type] = ???

  def evalEnumExpr(localVars: Map[VarName, Type], store: TypeStore, enum: Enum): TypeMemories[Type] = ???

  def evalAssert(localVars: Map[VarName, Type], store: TypeStore, cond: Expr): TypeMemories[Type] = ???

  def evalLocalAll(localVars: Map[VarName, Type], store: TypeStore, exprs: Seq[Expr]): TypeMemories[List[Type]] = {
    exprs.toList.foldLeft[TypeMemories[List[Type]]](TypeMemories(Set(TypeMemory(SuccessResult(List()), store)))) { (mems, e) =>
      val flatMems = Lattice[TypeMemories[Flat[List[Type]]]].lub(mems.memories.flatMap[TypeMemories[Flat[List[Type]]], Set[TypeMemories[Flat[List[Type]]]]] { case TypeMemory(prevres, store__) =>
        prevres match {
          case SuccessResult(tys) =>
            val emems = evalLocal(localVars, store__, e)
            Set(TypeMemories(emems.memories.map[TypeMemory[Flat[List[Type]]], Set[TypeMemory[Flat[List[Type]]]]] {
              case TypeMemory(res, store_) =>
                res match {
                  case SuccessResult(ty) =>
                    TypeMemory(SuccessResult(FlatValue(tys :+ ty)), store_)
                  case ExceptionalResult(exres) => TypeMemory(ExceptionalResult(exres), store_)
                }
            }))
          case ExceptionalResult(exres) =>
            Set(TypeMemories[Flat[List[Type]]](Set(TypeMemory(ExceptionalResult(exres), store__))))
        }
      })
      TypeMemories(flatMems.memories.map {
        case TypeMemory(res, st) =>
          TypeMemory(res match {
            case SuccessResult(t) => SuccessResult(Flat.unflat(t))
            case ExceptionalResult(exres) => ExceptionalResult(exres)
          }, st)
      }) // Remove dummy Flat, since all merger of successes happens manually
    }
  }

  def evalLocal(localVars: Map[VarName, Type], store: TypeStore, expr: Expr): TypeMemories[Type] = {
    expr match {
      case BasicExpr(b) => TypeMemories(Set(TypeMemory(SuccessResult(BaseType(typing.inferType(b))), store)))
      case VarExpr(x) => evalVar(store, x)
      case FieldAccExpr(target, fieldName) => evalFieldAccess(localVars, store, target, fieldName)
      case UnaryExpr(op, operand) => evalUnary(localVars, store, op, operand)
      case BinaryExpr(left, op, right) => evalBinary(localVars, store, left, op, right)
      case ConstructorExpr(name, args) => evalConstructor(localVars, store, name, args)
      case ListExpr(elements) => evalList(localVars, store, elements)
      case SetExpr(elements) => evalSet(localVars, store, elements)
      case MapExpr(keyvalues) => evalMap(localVars, store, keyvalues)
      case MapLookupExpr(emap, ekey) => evalMapLookup(localVars, store, emap, ekey)
      case MapUpdExpr(emap, ekey, evl) => evalMapUpdate(localVars, store, emap, ekey, evl)
      case FunCallExpr(functionName, args) => evalFunCall(localVars, store, functionName, args)
      case ReturnExpr(evl) => evalReturn(localVars, store, evl)
      case AssignExpr(assgn, targetexpr) => evalAssign(localVars, store, assgn, targetexpr)
      case IfExpr(cond, thenB, elseB) => evalIf(localVars, store, cond, thenB, elseB)
      case SwitchExpr(scrutinee, cases) => evalSwitch(localVars, store, scrutinee, cases)
      case VisitExpr(strategy, scrutinee, cases) => evalVisit(localVars, store, strategy, scrutinee, cases)
      case BreakExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Break), store)))
      case ContinueExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Continue), store)))
      case FailExpr => TypeMemories(Set(TypeMemory(ExceptionalResult(Fail), store)))
      case LocalBlockExpr(vardefs, exprs) => evalBlock(localVars, store, vardefs, exprs)
      case ForExpr(enum, body) => evalFor(localVars, store, enum, body)
      case WhileExpr(cond, body) => evalWhile(localVars, store, cond, body)
      case SolveExpr(vars, body) => evalSolve(localVars, store, vars, body)
      case ThrowExpr(evl) => evalThrow(localVars, store, evl)
      case TryCatchExpr(tryB, catchVar, catchB) => evalTryCatch(localVars, store, tryB, catchVar, catchB)
      case TryFinallyExpr(tryB, finallyB) => evalTryFinally(localVars, store, tryB, finallyB)
      case EnumExpr(enum) => evalEnumExpr(localVars, store, enum)
      case AssertExpr(cond) => evalAssert(localVars, store, cond)
    }
  }

  def eval(store: TypeStore, expr: Expr): TypeMemories[Type] = evalLocal(Map.empty, store, expr)
}
