package semantics

import semantics.domains.abstracting._
import semantics.domains.abstracting.TypeMemory.TypeResult
import semantics.domains.common._
import semantics.domains.concrete.TypeOps._
import TypeMemory._
import syntax._

import scala.collection.immutable
import scalaz.syntax.traverse._
import scalaz.std.list._

// TODO: Convert lub(...flatMap) to map(...lub)
case class AbstractTypeExecutor(module: Module) {
  private
  val typing = Typing(module)

  private
  def getVar(store: TypeStore, x: VarName): Option[(Boolean, Type)] = store match {
    case TypeStoreV(storemap) => storemap.get(x)
    case TypeStoreTop => Some((true, Lattice[Type].top))
  }

  private
  def setVar(store: TypeStore, x: VarName, typ: Type): TypeStore = store match {
    case TypeStoreV(st) => TypeStoreV(st.updated(x, (false, typ)))
    case TypeStoreTop => TypeStoreTop
  }

  private
  def setVars(store: TypeStore, env: Map[VarName, Type]): TypeStore =
    env.foldLeft(store) { (store_, varval) =>
      val (x, vl) = varval
      setVar(store_, x, vl)
    }

  private
  def dropVars(store : TypeStore, xs: Set[VarName]): TypeStore = store match {
    case TypeStoreV(st) => TypeStoreV(st -- xs)
    case TypeStoreTop => TypeStoreTop
  }

  private
  def ifFail(res: TypeResult[Type], typ: Type): TypeResult[Type] = res match {
    case ExceptionalResult(Fail) => SuccessResult(typ)
    case _ => res
  }

  private
  def reconstruct(scrtyp: Type, cvtys: List[Type]): Set[TypeResult[Type]] =
    scrtyp match {
      case BaseType(b) =>
        if (cvtys.isEmpty) Set(SuccessResult(BaseType(b)))
        else Set(ExceptionalResult(Error(ReconstructError(scrtyp, cvtys))))
      case DataType(name) =>
        module.datatypes(name).toSet[ConsName].flatMap[TypeResult[Type], Set[TypeResult[Type]]] { cons =>
          val (_, parameters) = module.constructors(cons)
          val zipped = cvtys.zip(parameters.map(_.typ))
          if (cvtys.length == parameters.length &&
                zipped.forall { case (ty1, ty2) => possiblySubtype(ty1, ty2) }) {
            val posEx =
              if (zipped.exists { case (ty1, ty2) => possibleNotSubtype(ty1, ty2) })
                Set(ExceptionalResult[Type, Type](Error(ReconstructError(scrtyp, cvtys))))
              else Set()
            posEx ++ Set(SuccessResult(scrtyp))
          }
          else Set(ExceptionalResult[Type, Type](Error(ReconstructError(scrtyp, cvtys))))
        }
      case ListType(elementType) =>
        Set(SuccessResult(ListType(Lattice[Type].lub(cvtys.toSet))))
      case SetType(elementType) =>
        Set(SuccessResult(SetType(Lattice[Type].lub(cvtys.toSet))))
      case MapType(keyType, valueType) =>
        val newKeyType = Lattice[Type].lub(cvtys.take(cvtys.length/2).toSet)
        val newValType = Lattice[Type].lub(cvtys.drop(cvtys.length/2).toSet)
        Set(SuccessResult(MapType(newKeyType, newValType)))
      case VoidType =>
        if (cvtys.isEmpty) Set(SuccessResult(VoidType))
        else Set(ExceptionalResult(Error(ReconstructError(scrtyp, cvtys))))
      case ValueType =>
        Set(ExceptionalResult(Error(ReconstructError(scrtyp, cvtys))), SuccessResult(ValueType))
    }

  private
  def possiblySubtype(typ1: Type, typ2: Type): Boolean = typing.isSubType(typ1, typ2) || (typ1 == ValueType)

  private
  def possibleNotSubtype(typ1: Type, typ2: Type): Boolean = !typing.isSubType(typ1, typ2)

  private
  def possiblyEqTyps(typ1: Type, typ2: Type): Boolean = typ1 match {
    case BaseType(IntType) => typ2 match {
      case BaseType(IntType) | ValueType => true
      case _ => false
    }
    case BaseType(StringType) => typ2 match {
      case BaseType(StringType) | ValueType => true
      case _ => false
    }
    case DataType(name1) => typ2 match {
      case DataType(name2) if name1 == name2 => true
      case ValueType => true
      case _ => false
    }
    case ListType(ety1) => typ2 match {
      case ListType(ety2) => possiblyEqTyps(ety1, ety2)
      case ValueType => true
      case _ => false
    }
    case SetType(ety1) => typ2 match {
      case SetType(ety2) => possiblyEqTyps(ety1, ety2)
      case ValueType => true
      case _ => false
    }
    case MapType(kty1, vty1) => typ2 match {
      case MapType(kty2, vty2) => possiblyEqTyps(kty1, kty2) && possiblyEqTyps(vty1, vty2)
      case ValueType => true
      case _ => false
    }
    case VoidType => typ2 match { // TODO Check correctness w.r.t. bottom
      case VoidType | ValueType => true
      case _ => false
    }
    case ValueType => true
  }

  // Use Set instead of Stream for nicer equality, and easier structural traversal when having alternatives
  def mergePairs(pairs: Set[(Map[VarName, Type], Map[VarName, Type])]): Set[Set[Map[VarName, Type]]] = {
    // TODO Seems to lose the laziness, but I am still unsure how to recover that
    pairs.flatMap { case (env1, env2) =>
      if (env1.keySet.intersect(env2.keySet).forall(x => possiblyEqTyps(env1(x), env2(x))))
        Set[Set[Map[VarName, Type]]](Set(), Set(env1 ++ env2))
      else Set[Set[Map[VarName, Type]]](Set())
    }
  }

  def merge(envss: List[Set[Map[VarName, Type]]]): Set[Set[Map[VarName, Type]]] = {
    envss.foldLeft[Set[Set[Map[VarName, Type]]]](Set(Set(Map()))) { (envsset, merged) =>
      envsset.flatMap { envs =>
        val pairsEnvs = envs.flatMap(env => merged.map(menv => (env, menv)))
        mergePairs(pairsEnvs)
      }
    }
  }

  def matchPattAll(store: TypeStore, scrtyp: Type, spatts: List[StarPatt], construct: Type => Type): Set[Set[Map[syntax.VarName, Type]]] = {
    spatts match {
      case Nil => Set(Set(), Set(Map()))
      case sp :: sps =>
        sp match {
          case OrdinaryPatt(p) =>
            Set(Set[Map[VarName, Type]]()) ++
              matchPatt(store, scrtyp, p).flatMap { envp =>
                matchPattAll(store, scrtyp, sps, construct).flatMap { envps =>
                  merge(List(envp, envps))
                }
              }
          case ArbitraryPatt(sx) =>
            getVar(store, sx).fold {
              matchPattAll(setVar(store, sx, construct(scrtyp)), scrtyp, sps, construct)
            } { case (_, sxtyp) =>
                if (possiblyEqTyps(scrtyp, sxtyp))
                  Set(Set[Map[VarName, Type]]()) ++ matchPattAll(store, scrtyp, sps, construct)
                else Set(Set())
            }
        }
    }
  }

  def typeChildren(ty: Type): Set[List[Type]] = ty match {
    case BaseType(_) => Set(List())
    case DataType(name) =>
      module.datatypes(name).map(module.constructors).map(_._2.map(_.typ)).toSet
    case ListType(elementType) => Set(List(elementType))
    case SetType(elementType) => Set(List(elementType))
    case MapType(keyType, valueType) => Set(List(keyType, valueType))
    case VoidType => Set(List())
    case ValueType => Set(List(ValueType))
      // It can have any child, and for current analysis there is no point in duplication of the same type
  }

  def matchPatt(store: TypeStore, scrtyp: Type, cspatt: Patt): Set[Set[Map[syntax.VarName, Type]]] = cspatt match {
    case BasicPatt(b) =>
      b match {
        case IntLit(_) => scrtyp match {
          case BaseType(IntType) | ValueType => Set(Set(),Set(Map()))
          case _ => Set(Set())
        }
        case StringLit(_) => scrtyp match {
          case BaseType(StringType) | ValueType => Set(Set(), Set(Map()))
          case _ => Set(Set())
        }
      }
    case IgnorePatt => Set(Set(Map()))
    case VarPatt(name) =>
      getVar(store, name).fold[Set[Set[Map[VarName, Type]]]](Set(Set(Map(name -> scrtyp)))) { case (_, xtyp) =>
          if (possiblyEqTyps(scrtyp, xtyp)) Set(Set(), Set(Map()))
          else Set(Set())
      }
    case ConstructorPatt(consname, pats) =>
      val (dt, pars) = module.constructors(consname)
      def posMatch = {
          val matched = pats.toList.zip(pars.map(_.typ)).traverseU { case (p,t) => matchPatt(store, t, p).toList }.toSet
          matched.flatMap(merge)
        }
      scrtyp match {
        case DataType(name) if name == dt =>
          (if (module.constructors.size == 1) Set[Set[Map[VarName,Type]]]()
           else Set(Set[Map[VarName, Type]]())) ++ posMatch
        case ValueType => Set(Set[Map[VarName, Type]]()) ++ posMatch
        case _ => Set(Set())
      }
    case LabelledTypedPatt(typ, labelVar, patt) =>
      if (possiblySubtype(scrtyp, typ)) {
        val posEx = if (possibleNotSubtype(scrtyp, typ)) Set(Set[Map[VarName, Type]]()) else Set()
        val inmatchs = matchPatt(store, scrtyp, patt)
        posEx ++ inmatchs.flatMap(inmatch => merge(List(Set(Map(labelVar -> scrtyp)), inmatch)))
      } else Set(Set())
    case ListPatt(spatts) =>
      scrtyp match {
        case ListType(elementType) => matchPattAll(store, elementType, spatts.toList, ListType)
        case ValueType => Set(Set[Map[VarName, Type]]()) ++ matchPattAll(store, ValueType, spatts.toList, ListType)
        case _ => Set(Set())
      }
    case SetPatt(spatts) =>
      scrtyp match {
        case SetType(elementType) => matchPattAll(store, elementType, spatts.toList, SetType)
        case ValueType => Set(Set[Map[VarName, Type]]()) ++ matchPattAll(store, ValueType, spatts.toList, SetType)
        case _ => Set(Set())
      }
    case NegationPatt(patt) =>
      matchPatt(store, scrtyp, patt).map { envs =>
        if (envs.isEmpty) Set(Map[VarName, Type]()) else Set[Map[VarName, Type]]()
      }
    case DescendantPatt(patt) =>
      type Res = Set[Set[Map[syntax.VarName, Type]]]
      def memoFix(typ: Type, memo: Map[Type, Res]): Res  = {
        def go(prevres: Res): Res = {
          val newres = matchPatt(store, typ, patt).flatMap { selfenvs =>
            typeChildren(typ).flatMap { chtyps =>
              chtyps.flatMap { cty =>
                val cenvss = memoFix(cty, memo.updated(typ, prevres))
                cenvss.map { cenv =>
                  selfenvs ++ cenv
                }
              }
            }
          }
          if (newres == prevres) newres
          else go(prevres union newres)
        }
        memo.getOrElse(typ, go(Set()))
      }
      memoFix(scrtyp, Map())
  }

  def evalVar(store: TypeStore, x: VarName): TypeMemories[Type] = {
    val unassignedError = Set(TypeMemory[Type](ExceptionalResult(Error(UnassignedVarError(x))), store))
    getVar(store, x).fold(TypeMemories(unassignedError)) {
      case (possUnassigned, typ) =>
        TypeMemories((if (possUnassigned) unassignedError else Set()) ++ Set(TypeMemory(SuccessResult(typ), store)))
    }
  }

  private
  def unflatMems[A](flatMems: TypeMemories[Flat[A]]): TypeMemories[A] = {
    TypeMemories(flatMems.memories.map {
      case TypeMemory(res, st) =>
        TypeMemory(res match {
          case SuccessResult(t) => SuccessResult(Flat.unflat(t))
          case ExceptionalResult(exres) => ExceptionalResult(exres)
        }, st)
    })
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
    case ("!", DataType("Bool")) => Set(SuccessResult(DataType("Bool")))
    case ("!", ValueType) =>
      Set(ExceptionalResult(Error(InvalidOperationError(op, List(vl))))) ++ Set(SuccessResult(DataType("Bool")))
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
      case (_, "==", _) => Set(SuccessResult(DataType("Bool")))
      case (_, "!=", _) => Set(SuccessResult(DataType("Bool")))
      case (_, "in", ListType(_)) => Set(SuccessResult(DataType("Bool")))
      case (_, "in", SetType(_)) => Set(SuccessResult(DataType("Bool")))
      case (_ , "in", MapType(_, _)) => Set(SuccessResult(DataType("Bool")))
      case (_ , "in", ValueType) => Set(invOp, SuccessResult(DataType("Bool")))
      case (lhvl, "notin", rhvl) => evalBinaryOp(lhvl, "in", rhvl).flatMap[TypeResult[Type], Set[TypeResult[Type]]] {
        case SuccessResult(ty) => evalUnaryOp("!", ty)
        case ExceptionalResult(exres) => Set(ExceptionalResult(exres))
      }
      case (DataType("Bool"), "&&", DataType("Bool")) =>
        Set(SuccessResult(DataType("Bool")))
      case (ValueType | DataType("Bool"), "&&", ValueType | DataType("Bool")) =>
        Set(invOp, SuccessResult(DataType("Bool")))
      case (DataType("Bool"), "||", DataType("Bool")) =>
        Set(SuccessResult(DataType("Bool")))
      case (ValueType | DataType("Bool"), "||", ValueType | DataType("Bool")) =>
        Set(invOp, SuccessResult(DataType("Bool")))
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
        Set(ExceptionalResult(Throw(DataType("DivByZero"))), SuccessResult(BaseType(IntType)))
      case (ValueType | BaseType(IntType), "/", ValueType | BaseType(IntType)) =>
        Set(invOp, ExceptionalResult(Throw(DataType("DivByZero"))), SuccessResult(BaseType(IntType)))
      case (BaseType(IntType), "%", BaseType(IntType)) =>
        Set(ExceptionalResult(Throw(DataType("ModNonPos"))), SuccessResult(BaseType(IntType)))
      case (ValueType | BaseType(IntType), "%", ValueType | BaseType(IntType)) =>
        Set(invOp, ExceptionalResult(Throw(DataType("ModNonPos"))), SuccessResult(BaseType(IntType)))
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
                  tysparszipped.forall { case (ty1, ty2) => possiblySubtype(ty1, ty2) }) {
              val sucsRes: TypeMemory[Type] = TypeMemory(SuccessResult(DataType(tyname)), store_)
              if (tysparszipped.exists { case (ty1, ty2) => possibleNotSubtype(ty1, ty2) })
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
                    if (possiblySubtype(actualKeyType, keyType)) {
                      val posEx = if (possibleNotSubtype(actualKeyType, keyType))
                                       Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(Throw(DataType("NoKey"))), store_))))
                                  else Set[TypeMemories[Type]]()
                      posEx ++ Set(TypeMemories[Type](Set(TypeMemory(SuccessResult(valueType), store_))))
                    }
                    else Set(TypeMemories(Set(TypeMemory(ExceptionalResult(Throw(DataType("NoKey"))), store_))))
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

  def evalFunCall(localVars: Map[VarName, Type], store: TypeStore, functionName: VarName, args: Seq[Expr]): TypeMemories[Type] = {
    val argmems = evalLocalAll(localVars, store, args)
    Lattice[TypeMemories[Type]].lub(argmems.memories.map { case TypeMemory(argres, store__) =>
      argres match {
        case SuccessResult(argtys) =>
          val (funresty, funpars, funbody) = module.funs(functionName)
          val argpartyps = argtys.zip(funpars.map(_.typ))
          val errRes = TypeMemory[Type](ExceptionalResult(Error(SignatureMismatch(functionName, argtys, funpars.map(_.typ)))), store__)
          if (argtys.length == funpars.length &&
                argpartyps.forall { case (ty1, ty2) => possiblySubtype(ty1, ty2) }) {
            val posEx = if (argpartyps.exists { case (ty1, ty2) => possibleNotSubtype(ty1, ty2) })
                            TypeMemories[Type](Set(errRes))
                        else Lattice[TypeMemories[Type]].bot
            val callRes: TypeMemories[Type] = {
              val callstore = TypeStoreV(module.globalVars.map { case (x, _) => x -> getVar(store__, x).get } ++
                funpars.map(_.name).zip(argtys.map(false -> _)).toMap)
              val resmems = funbody match {
                case ExprFunBody(exprfunbody) =>
                    evalLocal(funpars.map(par => par.name -> par.typ).toMap, callstore, exprfunbody)
                case PrimitiveFunBody =>
                  functionName match {
                    case "delete" =>
                      val (_, mapty) = callstore.vals("emap")
                      val (_, keyty) = callstore.vals("ekey")
                      mapty match {
                        case MapType(kty, vty) =>
                          TypeMemories[Type](Set(TypeMemory(SuccessResult(MapType(kty, vty)), callstore)))
                        case _ => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(Error(OtherError)), callstore)))
                      }
                    case "toString" =>
                      val arg = callstore.vals("earg")
                      TypeMemories[Type](Set(TypeMemory(SuccessResult(BaseType(StringType)), callstore)))
                    case _ => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(Error(OtherError)), callstore)))
                  }
              }
              Lattice[TypeMemories[Type]].lub(resmems.memories.map { case TypeMemory(res, resstore) =>
                val store_ =
                  Lattice[TypeStore].lub(TypeStoreV(module.globalVars.map { case (x, _) => x -> getVar(resstore, x).get }), store__)
                def funcallsuccess(restyp: Type): TypeMemories[Type] = {
                  val errRes = TypeMemory[Type](ExceptionalResult(Error(TypeError(restyp, funresty))), store_)
                  if (possiblySubtype(restyp, funresty)) {
                    val posEx = if (possibleNotSubtype(restyp, funresty)) TypeMemories[Type](Set(errRes))
                                else Lattice[TypeMemories[Type]].bot
                    Lattice[TypeMemories[Type]].lub(posEx, TypeMemories[Type](Set(TypeMemory(SuccessResult(restyp), store_))))
                  }
                  else TypeMemories[Type](Set(errRes))
                }
                res match {
                  case SuccessResult(restyp) => funcallsuccess(restyp)
                  case ExceptionalResult(exres) =>
                    exres match {
                      case Return(restyp) => funcallsuccess(restyp)
                      case Break | Continue | Fail =>
                        TypeMemories[Type](Set(TypeMemory(ExceptionalResult(Error(EscapedControlOperator)), store_)))
                      case _ => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_)))
                    }
                }
              })
            }
            Lattice[TypeMemories[Type]].lub(posEx, callRes)
          }
          else TypeMemories[Type](Set(errRes))
        case ExceptionalResult(exres) => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__)))
      }
    })
  }

  def evalReturn(localVars: Map[VarName, Type], store: TypeStore, evl: Expr): TypeMemories[Type] = {
    val valmems = evalLocal(localVars, store, evl)
    Lattice[TypeMemories[Type]].lub(valmems.memories.flatMap { case TypeMemory(valres, store_) =>
      valres match {
        case SuccessResult(valty) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(Return(valty)), store_))))
        case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
      }
    })
  }

  def evalAssignable(localVars: Map[VarName, Type], store: TypeStore, assgn: Assignable): TypeMemories[DataPath[Type]] = {
    assgn match {
      case VarAssgn(name) => TypeMemories(Set(TypeMemory(SuccessResult(DataPath(name, List())),store)))
      case FieldAccAssgn(target, fieldName) =>
        val targetmems = evalAssignable(localVars, store, target)
        val flatmems = Lattice[TypeMemories[Flat[DataPath[Type]]]].lub(targetmems.memories.flatMap[TypeMemories[Flat[DataPath[Type]]], Set[TypeMemories[Flat[DataPath[Type]]]]] {
          case TypeMemory(targetres, store_) =>
            targetres match {
              case SuccessResult(DataPath(vn, accessPaths)) =>
                Set(TypeMemories(Set(TypeMemory(SuccessResult(FlatValue(DataPath(vn, accessPaths :+ FieldAccessPath(fieldName)))), store_))))
              case ExceptionalResult(exres) =>
                Set(TypeMemories[Flat[DataPath[Type]]](Set(TypeMemory(ExceptionalResult(exres), store_))))
            }
        })
        unflatMems(flatmems)
      case MapUpdAssgn(target, ekey) =>
        val targetmems = evalAssignable(localVars, store, target)
        val flatmems = Lattice[TypeMemories[Flat[DataPath[Type]]]].lub(targetmems.memories.flatMap[TypeMemories[Flat[DataPath[Type]]], Set[TypeMemories[Flat[DataPath[Type]]]]] {
          case TypeMemory(targetres, store__) =>
            targetres match {
              case SuccessResult(DataPath(vn, accessPaths)) =>
                val keymems = evalLocal(localVars, store__, ekey)
                Set(TypeMemories(keymems.memories.map { case TypeMemory(keyres, store_) =>
                  keyres match {
                    case SuccessResult(keyt) =>
                      TypeMemory[Flat[DataPath[Type]]](SuccessResult(FlatValue(DataPath(vn, accessPaths :+ MapAccessPath(keyt)))), store_)
                    case ExceptionalResult(exres) => TypeMemory[Flat[DataPath[Type]]](ExceptionalResult(exres), store_)
                  }
                }))
              case ExceptionalResult(exres) =>
                Set(TypeMemories[Flat[DataPath[Type]]](Set(TypeMemory(ExceptionalResult(exres), store__))))
            }
        })
        unflatMems(flatmems)
    }
  }

  def updatePath(otyp: Type, paths: List[AccessPath[Type]], typ: Type): Set[TypeResult[Type]] = paths match {
    case Nil => Set(SuccessResult(typ))
    case path :: rpaths =>
      path match {
        case MapAccessPath(ktyp) =>
          def updateOnMap(keyType: Type, valueType: Type): Set[TypeResult[Type]] = {
            if (possiblySubtype(ktyp, keyType)) {
              Set(ExceptionalResult(Throw(DataType("NoKey")))) ++
                updatePath(valueType, rpaths, typ).map {
                  case SuccessResult(ntyp) =>
                    SuccessResult(MapType(Lattice[Type].lub(ktyp, keyType), Lattice[Type].lub(ntyp, valueType)))
                  case ExceptionalResult(exres) =>
                    ExceptionalResult(exres)
                }
            } else {
              Set(ExceptionalResult(Throw(DataType("NoKey"))))
            }
          }
          val exRes: TypeResult[Type] = ExceptionalResult(Error(TypeError(otyp, MapType(ktyp, typ))))
          otyp match {
            case MapType(keyType, valueType) => updateOnMap(keyType, valueType)
            case ValueType => Set(exRes) ++ updateOnMap(ValueType, ValueType)
            case _ => Set(exRes)
          }
        case FieldAccessPath(fieldName) =>
          def updateFieldOnType(dtname: TypeName): Set[TypeResult[Type]] = {
            val conss = module.datatypes(dtname)
            conss.toSet[ConsName].flatMap[TypeResult[Type], Set[TypeResult[Type]]] { cons =>
              val (_, pars) = module.constructors(cons)
              val index = pars.indexWhere(_.name == fieldName)
              if (index < 0) { Set(ExceptionalResult(Error(FieldError(otyp, fieldName)))) }
              else {
                updatePath(pars(index).typ, rpaths, typ).flatMap[TypeResult[Type], Set[TypeResult[Type]]] {
                  case SuccessResult(ntyp) =>
                    if (possiblySubtype(ntyp, pars(index).typ)) {
                      val posEx = if (possibleNotSubtype(ntyp, pars(index).typ))
                                      Set(ExceptionalResult(Error(TypeError(ntyp, pars(index).typ))))
                                  else Set()
                      posEx ++ Set(SuccessResult(DataType(dtname)))
                    } else Set(ExceptionalResult(Error(TypeError(ntyp, pars(index).typ))))
                  case ExceptionalResult(exres) => Set(ExceptionalResult(exres))
                }
              }
            }
          }
          otyp match {
            case DataType(name) => updateFieldOnType(name)
            case ValueType =>
              Set(ExceptionalResult(Error(FieldError(otyp, fieldName)))) ++ module.datatypes.keySet.filter { dt =>
                module.datatypes(dt).exists { cons =>
                  val (_, pars) = module.constructors(cons)
                  pars.exists(_.name == fieldName)
                }
              }.flatMap(updateFieldOnType)
            case _ => Set(ExceptionalResult(Error(FieldError(otyp, fieldName))))
          }
      }
  }

  def evalAssign(localVars: Map[VarName, Type], store: TypeStore, assgn: Assignable, targetexpr: Expr): TypeMemories[Type] = {
    val assignablemems = evalAssignable(localVars, store, assgn)
    Lattice[TypeMemories[Type]].lub(assignablemems.memories.flatMap { case TypeMemory(assgnres, store__) =>
        assgnres match {
          case SuccessResult(path) =>
            val targetmems = evalLocal(localVars, store__, targetexpr)
            Set(Lattice[TypeMemories[Type]].lub(targetmems.memories.flatMap{ case TypeMemory(targetres, store_) =>
              targetres match {
                case SuccessResult(typ) =>
                  val newTypRes: Set[TypeResult[Type]] =
                    if (path.accessPaths.isEmpty) {
                      Set(SuccessResult(typ))
                    } else {
                      getVar(store_, path.varName).fold[Set[TypeResult[Type]]](Set(ExceptionalResult(Error(UnassignedVarError(path.varName))))) {
                        case (possUnassigned, otyp) =>
                          (if (possUnassigned) Set(ExceptionalResult(Error(UnassignedVarError(path.varName)))) else Set()) ++
                            updatePath(otyp, path.accessPaths, typ)
                      }
                    }
                  newTypRes.flatMap {
                    case SuccessResult(newTyp) =>
                      // TODO provide internal error instead of exception
                      val staticVarTy = if (localVars.contains(path.varName)) localVars(path.varName) else module.globalVars(path.varName)
                      val exRes = TypeMemory[Type](ExceptionalResult(Error(TypeError(newTyp, staticVarTy))), store_)
                      if (possiblySubtype(newTyp, staticVarTy)) {
                        val posExRes = if (possibleNotSubtype(newTyp, staticVarTy)) Set(TypeMemories(Set(exRes))) else Set()
                        posExRes ++ Set(TypeMemories(Set(TypeMemory(SuccessResult(newTyp), setVar(store_, path.varName, newTyp)))))
                      }
                      else Set(TypeMemories[Type](Set(exRes)))
                    case ExceptionalResult(exres) =>
                      Set(TypeMemories[Type](Set(TypeMemory[Type](ExceptionalResult(exres), store_))))
                  }
                case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
              }
            }))
          case ExceptionalResult(exres) =>
            Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
        }
    })
  }

  def evalIf(localVars: Map[VarName, Type], store: TypeStore, cond: Expr, thenB: Expr, elseB: Expr): TypeMemories[Type] = {
    val condmems = evalLocal(localVars, store, cond)
    Lattice[TypeMemories[Type]].lub(condmems.memories.flatMap { case TypeMemory(condres, store__) =>
      condres match {
        case SuccessResult(condty) =>
          val exRes = TypeMemory[Type](ExceptionalResult(Error(TypeError(condty, DataType("Bool")))), store__)
          def sucRes = Lattice[TypeMemories[Type]].lub(evalLocal(localVars, store__, thenB), evalLocal(localVars, store__, elseB))
          condty match {
            case DataType("Bool") => Set(sucRes)
            case ValueType => Set(Lattice[TypeMemories[Type]].lub(TypeMemories[Type](Set(exRes)), sucRes))
            case _ => Set(TypeMemories[Type](Set(exRes)))
          }
        case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store))))
      }
    })
  }

  def evalCases(localVars: Map[VarName, Type], store: TypeStore, scrval: Type, cases: List[Case]): TypeMemories[Type] = {
    def evalCase(store: TypeStore, action: Expr, envs: Set[Map[VarName, Type]]): TypeMemories[Type] = {
      envs.headOption.fold(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(Fail), store)))) { env =>
        val actmems = evalLocal(localVars, setVars(store, env), action)
        Lattice[TypeMemories[Type]].lub(actmems.memories.map { case TypeMemory(actres, store_) =>
          actres match {
            case ExceptionalResult(Fail) => evalCase(store, action, envs.tail)
            case _ => TypeMemories[Type](Set(TypeMemory(actres, dropVars(store_, env.keySet))))
          }
        })
      }
    }
    cases match {
      case Nil => TypeMemories(Set(TypeMemory(ExceptionalResult(Fail), store)))
      case Case(cspatt, csaction) :: css =>
        val envss = matchPatt(store, scrval, cspatt)
        Lattice[TypeMemories[Type]].lub(envss.map { envs =>
          val casemems: TypeMemories[Type] = evalCase(store, csaction, envs)
          Lattice[TypeMemories[Type]].lub(casemems.memories.map { case TypeMemory(cres, store_) =>
            cres match {
              case ExceptionalResult(Fail) => evalCases(localVars, store, scrval, css)
              case _ => TypeMemories[Type](Set(TypeMemory(cres, store_)))
            }
          })
        })
    }
  }

  def evalSwitch(localVars: Map[VarName, Type], store: TypeStore, scrutinee: Expr, cases: Seq[Case]): TypeMemories[Type] = {
    val scrmems = evalLocal(localVars, store, scrutinee)
    Lattice[TypeMemories[Type]].lub(scrmems.memories.flatMap { case TypeMemory(scrres, store__) =>
        scrres match {
          case SuccessResult(scrval) =>
            val casemems: TypeMemories[Type] = evalCases(localVars, store__, scrval, cases.toList)
            Set(Lattice[TypeMemories[Type]].lub(casemems.memories.map { case TypeMemory(caseres, store_) =>
                caseres match {
                  case SuccessResult(caseval) =>
                    TypeMemories[Type](Set(TypeMemory(SuccessResult(caseval), store_)))
                  case ExceptionalResult(exres) =>
                    exres match {
                      case Fail => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_)))
                      case _ => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_)))
                    }
                }
            }))
          case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
        }
    })
  }

  def evalTD(localVars: Map[VarName, Type], store: TypeStore, scrtyp: Type, cases: List[Case], break: Boolean): TypeMemories[Type] = {
    def evalTDAll(types: List[Type], store: TypeStore, memo: Map[Type, TypeMemories[Type]]): TypeMemories[List[Type]] = {
      types match {
        case Nil => TypeMemories[List[Type]](Set(TypeMemory(SuccessResult(List()), store)))
        case cty::ctys =>
          val ctymems = memoFix(cty, store, memo)
          val flatmems = Lattice[TypeMemories[Flat[List[Type]]]].lub(ctymems.memories.map {
            case TypeMemory(ctyres, store__) =>
              ifFail(ctyres, cty) match {
                case SuccessResult(cty_) =>
                  if (break && ctyres != ExceptionalResult(Fail))
                    TypeMemories[Flat[List[Type]]](Set(TypeMemory(SuccessResult(FlatValue(cty_ :: ctys)), store__)))
                  else {
                    val ctysmems = evalTDAll(ctys, store__, memo)
                    TypeMemories(ctysmems.memories.map { case TypeMemory(ctysres, store_) =>
                        ctysres match {
                          case SuccessResult(ctys_) =>
                            TypeMemory[Flat[List[Type]]](SuccessResult(FlatValue(cty_ :: ctys_)), store_)
                          case ExceptionalResult(exres) =>
                            TypeMemory[Flat[List[Type]]](ExceptionalResult(exres), store_)
                        }
                    })
                  }
                case ExceptionalResult(exres) =>
                  TypeMemories[Flat[List[Type]]](Set(TypeMemory(ExceptionalResult(exres), store__)))
              }
          })
          unflatMems(flatmems)
      }
    }
    def memoFix(scrtyp: Type, store: TypeStore, memo: Map[Type, TypeMemories[Type]]): TypeMemories[Type] = {
      def go(prevRes: TypeMemories[Type]): TypeMemories[Type] = {
        val scmems = evalCases(localVars, store, scrtyp, cases)
        val newRes = Lattice[TypeMemories[Type]].lub(scmems.memories.map { case TypeMemory(scres, store__) =>
          ifFail(scres, scrtyp) match {
            case SuccessResult(typ) =>
              if (break && scres != ExceptionalResult(Fail)) {
                TypeMemories[Type](Set(TypeMemory(SuccessResult(typ), store__)))
              } else {
                val cvmems: Set[TypeMemories[List[Type]]] = typeChildren(typ).map(cts => evalTDAll(cts, store, memo.updated(scrtyp, prevRes)))
                Lattice[TypeMemories[Type]].lub(cvmems.flatMap(_.memories.map { case TypeMemory(cvres, store_) =>
                  cvres match {
                    case SuccessResult(cvtys) =>
                      val recons: Set[TypeResult[Type]] = reconstruct(scrtyp, cvtys)
                      Lattice[TypeMemories[Type]].lub(recons.map { tyres =>
                        TypeMemories[Type](Set(TypeMemory(tyres, store_)))
                      })
                    case ExceptionalResult(exres) => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_)))
                  }
                }))
              }
            case ExceptionalResult(exres) => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__)))
          }
        })
        if (Lattice[TypeMemories[Type]].<=(newRes, prevRes)) newRes
        else go(Lattice[TypeMemories[Type]].widen(prevRes, newRes, 10))
      }
      memo.getOrElse(scrtyp, go(Lattice[TypeMemories[Type]].bot))
    }
    memoFix(scrtyp, store, Map())
  }


  def evalBU(localVars: Map[VarName, Type], store: TypeStore, scrtyp: Type, cases: List[Case], break: Boolean): TypeMemories[Type] = {
    def evalBUAll(tys: List[Type], store: TypeStore, memo: Map[Type, TypeMemories[Type]]): TypeMemories[(Boolean, List[Type])] = {
      tys match {
        case Nil => TypeMemories[(Boolean, List[Type])](Set(TypeMemory(SuccessResult((true, List())), store)))
        case cty::ctys =>
          val ctymems = memoFix(store, cty, memo)
          val flatmems = Lattice[TypeMemories[Flat[(Boolean, List[Type])]]].lub(ctymems.memories.map {
            case TypeMemory(ctyres, store__) =>
              ifFail(ctyres, cty) match {
                case SuccessResult(cty_) =>
                  if (break && ctyres != ExceptionalResult(Fail))
                    TypeMemories[Flat[(Boolean, List[Type])]](
                      Set(TypeMemory(SuccessResult(FlatValue((false, cty_ :: ctys))), store__)))
                  else {
                    val ctysmems = evalBUAll(ctys, store__, memo)
                    TypeMemories[Flat[(Boolean, List[Type])]](ctysmems.memories.map { case TypeMemory(ctysres, store_) =>
                      ctysres match {
                        case SuccessResult((allfailed, ctys_)) =>
                          TypeMemory[Flat[(Boolean, List[Type])]](SuccessResult(
                            FlatValue((ctyres == ExceptionalResult(Fail) && allfailed, cty_ :: ctys_))), store_)
                        case ExceptionalResult(exres) =>
                          TypeMemory[Flat[(Boolean, List[Type])]](ExceptionalResult(exres), store_)
                      }
                    })
                  }
                case ExceptionalResult(exres) =>
                  TypeMemories[Flat[(Boolean, List[Type])]](Set(TypeMemory(ExceptionalResult(exres), store__)))
              }
          })
          unflatMems(flatmems)
      }
    }
    // TODO Types can possibly be infinitely wide, consider bounding parameter sizes of lists maps sets
    // TODO Maybe it is fine, since number of types in a particular program is bounded?
    def memoFix(store: TypeStore, scrtyp: Type, memo: Map[Type, TypeMemories[Type]]) = {
      def go(prevRes: TypeMemories[Type]): TypeMemories[Type] = {
        val ctymems: Set[TypeMemories[(Boolean, List[Type])]] = typeChildren(scrtyp).map(ctys =>
          evalBUAll(ctys, store, memo.updated(scrtyp, prevRes)))
        val newRes = Lattice[TypeMemories[Type]].lub(ctymems.flatMap(_.memories.map { case TypeMemory(ccres, store__) =>
          ccres match {
            case SuccessResult((allfailed, ctys)) =>
              if (break) {
                if (allfailed) evalCases(localVars, store__, scrtyp, cases)
                else Lattice[TypeMemories[Type]].lub(reconstruct(scrtyp, ctys).map(rcres =>
                  TypeMemories[Type](Set(TypeMemory(rcres, store__)))))
              } else Lattice[TypeMemories[Type]].lub(reconstruct(scrtyp, ctys).map {
                case SuccessResult(newty) =>
                  val selfmems = evalCases(localVars, store__, newty, cases)
                  Lattice[TypeMemories[Type]].lub(selfmems.memories.map { case TypeMemory(selfres, store_) =>
                    selfres match {
                      case ExceptionalResult(Fail) => TypeMemories[Type](Set(TypeMemory(SuccessResult(newty), store_)))
                      case _ => TypeMemories[Type](Set(TypeMemory(selfres, store_)))
                    }
                  })
                case ExceptionalResult(exres) => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__)))
              })
            case ExceptionalResult(exres) => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__)))
          }
        }))
        if (Lattice[TypeMemories[Type]].<=(newRes, prevRes)) newRes
        else go(Lattice[TypeMemories[Type]].widen(prevRes, newRes, 10))
      }
      memo.getOrElse(scrtyp, go(Lattice[TypeMemories[Type]].bot))
    }
    memoFix(store, scrtyp, Map())
  }

  def evalVisitStrategy(strategy: Strategy, localVars: Map[VarName, Type], store: TypeStore, scrtyp: Type, cases: List[Case]): TypeMemories[Type] = {
    def loop(store: TypeStore, scrtyp: Type, evalIn : (Map[VarName, Type], TypeStore, Type, List[Case], Boolean) => TypeMemories[Type]): TypeMemories[Type] = {
      def memoFix(store: TypeStore, scryp: Type, memo: Map[TypeStore, TypeMemories[Type]]): TypeMemories[Type] = {
        def go(prevRes: TypeMemories[Type]): TypeMemories[Type] = {
          val resmems = evalIn(localVars, store, scrtyp, cases, /* break = */ false)
          val newRes = Lattice[TypeMemories[Type]].lub(resmems.memories.map { case TypeMemory(res, store_) =>
            res match {
              case SuccessResult(resty) =>
                if (possiblyEqTyps(scrtyp, resty)) {
                  Lattice[TypeMemories[Type]].lub(TypeMemories[Type](
                    Set(TypeMemory(SuccessResult(resty), store_))),
                    memoFix(Lattice[TypeStore].widen(store, store_, 10), resty, memo.updated(store, prevRes)))
                } else {
                   memoFix(Lattice[TypeStore].widen(store, store_, 10), resty, memo.updated(store, prevRes))
                }
              case ExceptionalResult(exres) => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_)))
            }
          })
          if (Lattice[TypeMemories[Type]].<=(newRes, prevRes)) newRes
          else go(Lattice[TypeMemories[Type]].widen(prevRes, newRes, 10))
        }
        memo.getOrElse(store, go(Lattice[TypeMemories[Type]].bot))
      }
      memoFix(store, scrtyp, Map())
    }
    strategy match {
      case TopDown => evalTD(localVars, store, scrtyp, cases, break = false)
      case TopDownBreak => evalTD(localVars, store, scrtyp, cases, break = true)
      case BottomUp => evalBU(localVars, store, scrtyp, cases, break = false)
      case BottomUpBreak => evalBU(localVars, store, scrtyp, cases, break = true)
      case Innermost =>
        loop(store, scrtyp, evalBU)
      case Outermost =>
        loop(store, scrtyp, evalTD)
    }
  }

  def evalVisit(localVars: Map[VarName, Type], store: TypeStore, strategy: Strategy, scrutinee: Expr, cases: Seq[Case]): TypeMemories[Type] = {
    val scrmems = evalLocal(localVars, store, scrutinee)
    Lattice[TypeMemories[Type]].lub(scrmems.memories.map { case TypeMemory(scrres, store__) =>
      scrres match {
        case SuccessResult(scrtyp) =>
          val casemems: TypeMemories[Type] = evalVisitStrategy(strategy, localVars, store__, scrtyp, cases.toList)
          Lattice[TypeMemories[Type]].lub(casemems.memories.map { case TypeMemory(caseres, store_) =>
              caseres match {
                case SuccessResult(casetyp) => TypeMemories[Type](Set(TypeMemory(SuccessResult(casetyp), store_)))
                case ExceptionalResult(exres) =>
                  exres match {
                    case Fail => TypeMemories[Type](Set(TypeMemory(SuccessResult(scrtyp), store_)))
                    case _ => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_)))
                  }
              }
          })
        case ExceptionalResult(exres) => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__)))
      }
    })
  }

  def evalBlock(localVars: Map[VarName, Type], store: TypeStore, vardefs: Seq[Parameter], exprs: Seq[Expr]): TypeMemories[Type] = {
    val localVars_ = localVars ++ vardefs.map(par => par.name -> par.typ)
    val resmems = evalLocalAll(localVars_, store, exprs)
    Lattice[TypeMemories[Type]].lub(resmems.memories.map[TypeMemories[Type], Set[TypeMemories[Type]]] { case TypeMemory(res, store__) =>
        val store_ = dropVars(store__, vardefs.map(_.name).toSet)
        res match {
          case SuccessResult(typs) => TypeMemories(Set(TypeMemory(SuccessResult(typs.lastOption.getOrElse(VoidType)), store_)))
          case ExceptionalResult(exres) => TypeMemories(Set(TypeMemory(ExceptionalResult(exres), store_)))
        }
    })
  }

  def evalGenerator(localVars: Map[VarName, Type], store: TypeStore, gen: Generator): TypeMemories[Set[Set[Map[VarName, Type]]]] = {
    gen match {
      case MatchAssign(patt, target) =>
        val tmems = evalLocal(localVars, store, target)
        TypeMemories(tmems.memories.map { case TypeMemory(tres, store_) =>
          tres match {
            case SuccessResult(ttyp) => TypeMemory[Set[Set[Map[VarName, Type]]]](SuccessResult(matchPatt(store_, ttyp, patt)), store_)
            case ExceptionalResult(exres) => TypeMemory[Set[Set[Map[VarName, Type]]]](ExceptionalResult(exres), store_)
          }
        })
      case EnumAssign(varname, target) =>
        val tmems = evalLocal(localVars, store, target)
        val flatmems = Lattice[TypeMemories[Flat[Set[Set[Map[VarName, Type]]]]]].lub(
          tmems.memories.flatMap[TypeMemories[Flat[Set[Set[Map[VarName, Type]]]]], Set[TypeMemories[Flat[Set[Set[Map[VarName, Type]]]]]]] {
            case TypeMemory(tres, store_) =>
              tres match {
                case SuccessResult(ttyp) =>
                  ttyp match {
                    case ListType(elementType) =>
                      Set(TypeMemories(Set(TypeMemory(SuccessResult(FlatValue(Set(Set(Map(varname -> elementType))))), store_))))
                    case SetType(elementType) =>
                      Set(TypeMemories(Set(TypeMemory(SuccessResult(FlatValue(Set(Set(Map(varname -> elementType))))), store_))))
                    case MapType(keyType, _) =>
                      Set(TypeMemories(Set(TypeMemory(SuccessResult(FlatValue(Set(Set(Map(varname -> keyType))))), store_))))
                    case ValueType =>
                      Set(TypeMemories(Set(TypeMemory(ExceptionalResult(Error(NotEnumerableError(ttyp))), store_),
                        TypeMemory(SuccessResult(FlatValue(Set(Set(Map(varname -> ValueType))))), store_))))
                    case _ =>
                      Set(TypeMemories(Set(TypeMemory(ExceptionalResult(Error(NotEnumerableError(ttyp))), store_))))
                  }
                case ExceptionalResult(exres) =>
                  Set(TypeMemories[Flat[Set[Set[Map[VarName, Type]]]]](Set(TypeMemory(ExceptionalResult(exres), store_))))
              }
        })
        unflatMems(flatmems)
    }
  }

  def evalEach(localVars: Map[VarName, Type], store: TypeStore, envss: Set[Set[Map[VarName, Type]]], body: Expr): TypeMemories[Type] = {
    def evalOnEnv(envs: Set[Map[VarName, Type]]): TypeMemories[Type] = {
      // TODO Find a way to have the go fixedpoint calculation outside the inner memoization/regular tree calculation
      def memoFix(store: TypeStore, memo: Map[TypeStore, TypeMemories[Type]]): TypeMemories[Type] = {
        def go(prevRes: TypeMemories[Type]): TypeMemories[Type] = {
          def itermems: TypeMemories[Type] = {
            // We overapproximate order, cardinality and content, so we have to try all possible combinations in parallel
            val bodymems = Lattice[TypeMemories[Type]].lub(envs.map { env =>
              evalLocal(localVars, setVars(store, env), body)
            })
            Lattice[TypeMemories[Type]].lub(bodymems.memories.flatMap { case TypeMemory(bodyres, store_) =>
              bodyres match {
                case SuccessResult(_) =>
                  Set(memoFix(Lattice[TypeStore].widen(store, store_, 10), memo.updated(store, prevRes)))
                case ExceptionalResult(exres) =>
                  exres match {
                    case Break => Set(TypeMemories[Type](Set(TypeMemory(SuccessResult(VoidType), store_))))
                    case Continue =>
                      Set(memoFix(Lattice[TypeStore].widen(store, store_, 10), memo.updated(store, prevRes)))
                    // We have to try everything again because of possible duplicates (although perhaps, it should only be
                    // envs, because it is not possible to change alternative through an iteration
                    case _ => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
                  }
              }
            })

          }
          val newRes = Lattice[TypeMemories[Type]].lub(TypeMemories[Type](Set(TypeMemory(SuccessResult(VoidType), store))), itermems)
          if (Lattice[TypeMemories[Type]].<=(newRes, prevRes)) newRes
          else go(Lattice[TypeMemories[Type]].widen(prevRes, newRes, 10))
        }
        memo.getOrElse(store, go(Lattice[TypeMemories[Type]].bot))
      }
      memoFix(store, Map())
    }
    Lattice[TypeMemories[Type]].lub(envss.map { envs => evalOnEnv(envs) })
  }

  def evalFor(localVars: Map[VarName, Type], store: TypeStore, gen: Generator, body: Expr): TypeMemories[Type] = {
    val genmems = evalGenerator(localVars, store, gen)
    Lattice[TypeMemories[Type]].lub(genmems.memories.flatMap { case TypeMemory(genres, store__) =>
      genres match {
        case SuccessResult(envs) =>
          val bodymems = evalEach(localVars, store__, envs, body)
          Set(TypeMemories(bodymems.memories.map[TypeMemory[Type], Set[TypeMemory[Type]]] { case TypeMemory(bodyres, store_) =>
            bodyres match {
              case SuccessResult(_) => TypeMemory(SuccessResult(VoidType), store_)
              case ExceptionalResult(exres) => TypeMemory(ExceptionalResult(exres), store_)
            }
          }))
        case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
      }
    })
  }

  def evalWhile(localVars: Map[VarName, Type], store: TypeStore, cond: Expr, body: Expr): TypeMemories[Type] = {
    def memoFix(store: TypeStore, memo: Map[TypeStore, TypeMemories[Type]]): TypeMemories[Type] = {
      def go(prevRes: TypeMemories[Type]): TypeMemories[Type] = {
        val condmems = evalLocal(localVars, store, cond)
        val newRes = Lattice[TypeMemories[Type]].lub(condmems.memories.flatMap { case TypeMemory(condres, store__) =>
            condres match {
              case SuccessResult(condty) =>
                val errRes = TypeMemory[Type](ExceptionalResult(Error(TypeError(condty, DataType("Bool")))), store__)
                def succRes: TypeMemories[Type] = {
                  val falseRes = TypeMemories[Type](Set(TypeMemory(SuccessResult(VoidType), store__)))
                  val trueRes = {
                    val bodymems = evalLocal(localVars, store__, body)
                    Lattice[TypeMemories[Type]].lub(bodymems.memories.map { case TypeMemory(bodyres, store_) =>
                      bodyres match {
                        case SuccessResult(_) =>
                          memoFix(Lattice[TypeStore].widen(store, store_, 10), memo.updated(store, prevRes))
                        case ExceptionalResult(exres) =>
                          exres match {
                            case Break => TypeMemories[Type](Set(TypeMemory(SuccessResult(VoidType), store_)))
                            case Continue =>
                              memoFix(Lattice[TypeStore].widen(store, store_, 10), memo.updated(store, prevRes))
                            case _ => TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_)))
                          }
                      }
                    })
                  }
                  Lattice[TypeMemories[Type]].lub(falseRes, trueRes)
                }
                condty match {
                  case DataType("Bool") => Set(succRes)
                  case ValueType => Set(TypeMemories[Type](Set(errRes))) ++ Set(succRes)
                  case _ => Set(TypeMemories[Type](Set(errRes)))
                }
              case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
            }
        })
        if (Lattice[TypeMemories[Type]].<=(newRes, prevRes)) newRes
        else go(Lattice[TypeMemories[Type]].widen(prevRes, newRes, 10))
      }
      memo.getOrElse(store, go(Lattice[TypeMemories[Type]].bot))
    }
    memoFix(store, Map())
  }

  def evalSolve(localVars: Map[VarName, Type], store: TypeStore, vars: Seq[VarName], body: Expr): TypeMemories[Type] = {
    def memoFix(store: TypeStore, memo: Map[TypeStore, TypeMemories[Type]]): TypeMemories[Type] = {
      def go(prevRes: TypeMemories[Type]): TypeMemories[Type] = {
        val bodymems = evalLocal(localVars, store, body)
        val newRes = Lattice[TypeMemories[Type]].lub(bodymems.memories.flatMap { case TypeMemory(bodyres, store_) =>
          bodyres match {
            case SuccessResult(t) =>
              val prevVars = vars.toList.flatMap(x => getVar(store, x).map(_._2))
              val newVars = vars.toList.flatMap(x => getVar(store_, x).map(_._2))
              val prevEmptyVar = vars.exists(x => getVar(store, x).isEmpty)
              val newEmptyVar = vars.exists(x => getVar(store_, x).isEmpty)
              if (prevEmptyVar || newEmptyVar)
                Set(TypeMemories[Type](Set(TypeMemory[Type](ExceptionalResult(Error(OtherError)), store_))))
              else {
                val prevPosEmptyVar = vars.exists(x => getVar(store, x).fold(false)(_._1))
                val newPosEmptyVar = vars.exists(x => getVar(store, x).fold(false)(_._1))
                val posEx = if (prevPosEmptyVar || newPosEmptyVar)
                  Set(TypeMemories[Type](Set(TypeMemory[Type](ExceptionalResult(Error(OtherError)), store_))))
                else Set[TypeMemories[Type]]()
                if (prevVars.zip(newVars).forall { case (ty1, ty2) => possiblyEqTyps(ty1, ty2) }) {
                  posEx ++ Set(memoFix(Lattice[TypeStore].widen(store, store_, 10), memo.updated(store, prevRes))) ++
                    Set(TypeMemories[Type](Set(TypeMemory(SuccessResult(t), store_))))
                }
                else posEx ++ Set(memoFix(Lattice[TypeStore].widen(store, store_, 10), memo.updated(store, prevRes)))
              }
            case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
          }
        })
        if (Lattice[TypeMemories[Type]].<=(newRes, prevRes)) newRes
        else go(Lattice[TypeMemories[Type]].widen(prevRes, newRes, 10))
      }
      memo.getOrElse(store, go(Lattice[TypeMemories[Type]].bot))
    }
    memoFix(store, Map())
  }

  def evalThrow(localVars: Map[VarName, Type], store: TypeStore, evl: Expr): TypeMemories[Type] = {
    val valmems = evalLocal(localVars, store, evl)
    Lattice[TypeMemories[Type]].lub(valmems.memories.flatMap { case TypeMemory(valres, store_) =>
      valres match {
        case SuccessResult(valty) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(Throw(valty)), store_))))
        case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
      }
    })
  }

  def evalTryCatch(localVars: Map[VarName, Type], store: TypeStore, tryB: Expr, catchVar: VarName, catchB: Expr): TypeMemories[Type] = {
    val trymems = evalLocal(localVars, store, tryB)
    Lattice[TypeMemories[Type]].lub(trymems.memories.flatMap { case TypeMemory(tryres, store__) =>
        tryres match {
          case SuccessResult(trytyp) => Set(TypeMemories[Type](Set(TypeMemory(SuccessResult(trytyp), store__))))
          case ExceptionalResult(exres) =>
            exres match {
              case Throw(throwtyp) =>
                val store_ = setVar(store__, catchVar, throwtyp)
                Set(evalLocal(localVars, store_, catchB))
              case _ => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
            }
        }
    })
  }

  def evalTryFinally(localVars: Map[VarName, Type], store: TypeStore, tryB: Expr, finallyB: Expr): TypeMemories[Type] = {
    val trymems = evalLocal(localVars, store, tryB)
    Lattice[TypeMemories[Type]].lub(trymems.memories.flatMap { case TypeMemory(tryres, store__) =>
      tryres match {
        case SuccessResult(typ) =>
          val finmems = evalLocal(localVars, store, finallyB)
          Set(Lattice[TypeMemories[Type]].lub(finmems.memories.flatMap { case TypeMemory(finres, store_) =>
            finres match {
              case SuccessResult(_) => Set(TypeMemories[Type](Set(TypeMemory(SuccessResult(typ), store_))))
              case ExceptionalResult(exres) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store_))))
            }
          }))
        case ExceptionalResult(exres) =>
          exres match {
            case Throw(_) =>
              val finmems = evalLocal(localVars, store__, finallyB)
              Set(Lattice[TypeMemories[Type]].lub(finmems.memories.flatMap { case TypeMemory(finres, store_) =>
                finres match {
                  case SuccessResult(_) => Set(TypeMemories[Type](Set(TypeMemory(SuccessResult(VoidType), store_))))
                  case ExceptionalResult(exres_) => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres_), store_))))
                }
              }))
            case _ => Set(TypeMemories[Type](Set(TypeMemory(ExceptionalResult(exres), store__))))
          }
      }
    })
  }

  def evalAssert(localVars: Map[VarName, Type], store: TypeStore, cond: Expr): TypeMemories[Type] =
    throw new UnsupportedOperationException("Assertion Expression")

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
      unflatMems(flatMems) // Remove dummy Flat, since all merger of successes happens manually
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
      case AssertExpr(cond) => evalAssert(localVars, store, cond)
    }
  }

  def eval(store: TypeStore, expr: Expr): TypeMemories[Type] = evalLocal(Map.empty, store, expr)
}
