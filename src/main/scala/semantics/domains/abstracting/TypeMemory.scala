package semantics.domains.abstracting

import semantics.domains.abstracting.RefinementTypes._
import semantics.domains.abstracting.TypeStore.TypeResult
import semantics.domains.common._
import syntax.{Type, TypeName, VarName}
import util.Ref

sealed trait TypeStore
case object TypeStoreTop extends TypeStore
case class TypeStoreV(vals: Map[VarName, VoideableRefinementType]) extends TypeStore
case object TypeStoreBot extends TypeStore

case class TypeMemory[T](result: TypeResult[T], store: TypeStore)
case class TypeMemories[T](memories: Set[TypeMemory[T]])


object TypeStore {
  type TypeResult[T] = ResultV[VoideableRefinementType, T]

  def getVar(store: TypeStore, x: VarName): Option[VoideableRefinementType] = store match {
    case TypeStoreBot => None
    case TypeStoreV(storemap) => storemap.get(x)
    case TypeStoreTop => Some(RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].top)
  }

  def setVar(store: TypeStore, x: VarName, vrtyp: VoideableRefinementType): TypeStore = store match {
    case TypeStoreBot => TypeStoreBot
    case TypeStoreV(st) => TypeStoreV(st.updated(x, vrtyp))
    case TypeStoreTop => TypeStoreTop
  }

  def joinStores(store1: TypeStore, store2: TypeStore): TypeStore = {
    (store1, store2) match {
      case (TypeStoreBot, _) | (_, TypeStoreBot) => TypeStoreBot
      case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
        val allVars = vals1.keySet ++ vals2.keySet
        TypeStoreV(allVars.map { x =>
          if (vals2.contains(x)) {
            x -> vals2(x)
          } else {
            x -> vals1(x)
          }
        }.toMap)
      case _ => TypeStoreTop
    }
  }

  def dropVars(store : TypeStore, xs: Set[VarName]): TypeStore = store match {
    case TypeStoreBot => TypeStoreBot
    case TypeStoreV(st) => TypeStoreV(st -- xs)
    case TypeStoreTop => TypeStoreTop
  }

  implicit def TypeStoreLattice = new RSLattice[TypeStore, DataTypeDefs, RefinementDefs] {
    override def bot: TypeStore = TypeStoreBot

    override def top: TypeStore = TypeStoreTop

    private def upperBound(datatypes: DataTypeDefs, refinements: RefinementDefs, store1: TypeStore, store2: TypeStore,
                           tOp : (DataTypeDefs, RefinementDefs, VoideableRefinementType, VoideableRefinementType) => (RefinementDefs, VoideableRefinementType)): (RefinementDefs, TypeStore) = {
      (store1, store2) match {
        case (TypeStoreTop, _) | (_, TypeStoreTop) => (refinements, TypeStoreTop)
        case (TypeStoreBot, _) => (refinements, store2)
        case (_, TypeStoreBot) => (refinements, store1)
        case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
          val allVars = vals1.keySet ++ vals2.keySet
          val (newrefinements, varmap) = allVars.foldLeft((refinements, Map.empty[VarName, VoideableRefinementType])) { (st, x) =>
            val (prevrefinements, prevvarmap) = st
            vals1.get(x).fold((prevrefinements, prevvarmap.updated(x, VoideableRefinementType(possiblyVoid = true, vals2(x).refinementType)))) { vty1 =>
              vals2.get(x).fold((prevrefinements, prevvarmap.updated(x, VoideableRefinementType(possiblyVoid = true, vty1.refinementType)))) { vty2 =>
                val (newrefinements, newrefinetyp) = tOp(datatypes, prevrefinements, vty1, vty2)
                (newrefinements, prevvarmap.updated(x, newrefinetyp))
              }
            }
          }
          (newrefinements, TypeStoreV(varmap))
      }
    }

    override def lub(datatypes: DataTypeDefs, refinements: RefinementDefs, store1: TypeStore, store2: TypeStore): (RefinementDefs, TypeStore) = {
      upperBound(datatypes, refinements, store1, store2, RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].lub)
    }

    override def glb(datatypes: DataTypeDefs, refinements: RefinementDefs, store1: TypeStore, store2: TypeStore): (RefinementDefs, TypeStore) = {
      (store1, store2) match {
        case (TypeStoreBot, _) | (_, TypeStoreBot) => (refinements, TypeStoreBot)
        case (TypeStoreTop, _) => (refinements, store2)
        case (_, TypeStoreTop) => (refinements, store1)
        case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
          val sharedVars = vals1.keySet intersect vals2.keySet
          val (newrefinements, varmap) = sharedVars.foldLeft((refinements, Map.empty[VarName, VoideableRefinementType])) { (st, x) =>
            val (prevrefinements, prevvarmap) = st
            val vty1 = vals1(x)
            val vty2 = vals2(x)
            val (newrefinements, newrefinetyp) = RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].glb(datatypes, prevrefinements, vty1, vty2)
            (newrefinements, prevvarmap.updated(x, newrefinetyp))
          }
          (newrefinements, TypeStoreV(varmap))
      }
    }

    override def <=(datatypes: DataTypeDefs, refinements: RefinementDefs, store1: TypeStore, store2: TypeStore): Boolean = (store1, store2) match {
      case (_, TypeStoreTop) => true
      case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
        vals1.keySet.forall { x =>
          val vty1 = vals1(x)
          vals2.get(x).fold(false)(vty2 => RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].<=(datatypes, refinements, vty1, vty2))
        }
      case _ => false
    }

    override def widen(datatypes: DataTypeDefs, refinements: RefinementDefs, store1: TypeStore, store2: TypeStore, bound: Int): (RefinementDefs, TypeStore) =
      upperBound(datatypes, refinements, store1, store2, RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].widen(_, _, _, _, bound))
  }

}

case class TypeMemoriesOps(module: Module, refinements: Ref[RefinementDefs]) {
  val datatypes: DataTypeDefs = module.datatypes.mapValues(conss => module.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))

  implicit def TypeMemoriesLatticeFromRS[T](implicit rslattt: RSLattice[T, DataTypeDefs, RefinementDefs]) = new Lattice[TypeMemories[T]] {
    override def bot: TypeMemories[T] = TypeMemories(Set())

    override def top: TypeMemories[T] = {
      val topstore = RSLattice[TypeStore, DataTypeDefs, RefinementDefs].top
      TypeMemories(
        Set(TypeMemory(SuccessResult(RSLattice[T, DataTypeDefs, RefinementDefs].top), topstore)
          , TypeMemory(ExceptionalResult(Return(RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].top)), topstore)
          , TypeMemory(ExceptionalResult(Throw(RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].top)), topstore)
          , TypeMemory(ExceptionalResult(Break), topstore)
          , TypeMemory(ExceptionalResult(Continue), topstore)
          , TypeMemory(ExceptionalResult(Fail), topstore)
          , TypeMemory(ExceptionalResult(Error(Set(OtherError))), topstore)
        ))
    }

    private
    def groupMemories(a1: TypeMemories[T], a2: TypeMemories[T]): Set[List[TypeMemory[T]]] = {
      val grouped = (a1.memories.toList ++ a2.memories.toList).groupBy[String] {
        _.result match {
          case SuccessResult(_) => "SuccessResult"
          case ExceptionalResult(exres) =>
            exres match {
              case Return(_) => "Return"
              case Throw(_) => "Throw"
              case Break => "Break"
              case Continue => "Continue"
              case Fail => "Fail"
              case Error(_) => "Error"
            }
        }
      }
      grouped.values.toSet
    }

    private
    def upperBound(a1: TypeMemories[T], a2: TypeMemories[T],
                            storeOp: (DataTypeDefs, RefinementDefs, TypeStore, TypeStore) => (RefinementDefs, TypeStore),
                            tOp: (DataTypeDefs, RefinementDefs, T, T) => (RefinementDefs, T),
                            vrtOp: (DataTypeDefs, RefinementDefs, VoideableRefinementType, VoideableRefinementType) => (RefinementDefs, VoideableRefinementType)): TypeMemories[T] =
    {
      TypeMemories(groupMemories(a1, a2).flatMap[TypeMemory[T], Set[TypeMemory[T]]] {
        case ress@(List() | List(_)) => ress.toSet[TypeMemory[T]]
        case List(tmem1, tmem2) =>
          val (nrefinements1, nstore) = storeOp(datatypes, !refinements, tmem1.store, tmem2.store)
          refinements := nrefinements1
          tmem1.result match {
            case SuccessResult(t1) =>
              val SuccessResult(t2) = tmem2.result
              val (nrefinements2, tlub) = tOp(datatypes, !refinements, t1, t2)
              refinements := nrefinements2
              Set(TypeMemory[T](SuccessResult(tlub), nstore))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(vrty1) =>
                  val ExceptionalResult(Return(vrty2)) = tmem2.result
                  val (nrefinements2, vrtylub) = vrtOp(datatypes, !refinements, vrty1, vrty2)
                  refinements := nrefinements2
                  Set(TypeMemory[T](ExceptionalResult(Return(vrtylub)), nstore))
                case Throw(vrty1) =>
                  val ExceptionalResult(Throw(vrty2)) = tmem2.result
                  val (nrefinements2, vrtylub) = vrtOp(datatypes, !refinements, vrty1, vrty2)
                  refinements := nrefinements2
                  Set(TypeMemory[T](ExceptionalResult(Throw(vrtylub)), nstore))
                case Break =>
                  Set(TypeMemory[T](ExceptionalResult(Break), nstore))
                case Continue =>
                  Set(TypeMemory[T](ExceptionalResult(Continue), nstore))
                case Fail =>
                  Set(TypeMemory[T](ExceptionalResult(Fail), nstore))
                case Error(kinds1) =>
                  val ExceptionalResult(Error(kinds2)) = tmem2.result
                  Set(TypeMemory[T](ExceptionalResult(Error(kinds1 union kinds2)), nstore))
              }
          }
        case _ => throw NonNormalFormMemories
      })
    }

    override def lub(a1: TypeMemories[T], a2: TypeMemories[T]): TypeMemories[T] =
      upperBound(a1, a2, RSLattice[TypeStore, DataTypeDefs, RefinementDefs].lub,
        RSLattice[T, DataTypeDefs, RefinementDefs].lub, RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].lub)

    override def glb(a1: TypeMemories[T], a2: TypeMemories[T]): TypeMemories[T] =
      TypeMemories(groupMemories(a1, a2).flatMap[TypeMemory[T], Set[TypeMemory[T]]] {
        case List() | List(_) => Set()
        case List(tmem1, tmem2) =>
          val (nrefinements1, nstore) = RSLattice[TypeStore, DataTypeDefs, RefinementDefs].glb(datatypes, !refinements, tmem1.store, tmem2.store)
          refinements := nrefinements1
          tmem1.result match {
            case SuccessResult(t1) =>
              val SuccessResult(t2) = tmem2.result
              val (nrefinements2, tglb) = RSLattice[T, DataTypeDefs, RefinementDefs].glb(datatypes, !refinements, t1, t2)
              refinements := nrefinements2
              Set(TypeMemory[T](SuccessResult(tglb), nstore))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(vrt1) =>
                  val ExceptionalResult(Return(vrt2)) = tmem2.result
                  val (nrefinements2, vrtglb) = RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].glb(datatypes, !refinements, vrt1, vrt2)
                  refinements := nrefinements2
                  Set(TypeMemory[T](ExceptionalResult(Return(vrtglb)), nstore))
                case Throw(vrt1) =>
                  val ExceptionalResult(Throw(vrt2)) = tmem2.result
                  val (nrefinements2, vrtglb) = RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].glb(datatypes, !refinements, vrt1, vrt2)
                  refinements := nrefinements2
                  Set(TypeMemory[T](ExceptionalResult(Throw(vrtglb)), nstore))
                case Break => Set(TypeMemory[T](ExceptionalResult(Break), nstore))
                case Continue => Set(TypeMemory[T](ExceptionalResult(Continue), nstore))
                case Fail => Set(TypeMemory[T](ExceptionalResult(Fail), nstore))
                case Error(kinds1) =>
                  val ExceptionalResult(Error(kinds2)) = tmem2.result
                  Set(TypeMemory[T](ExceptionalResult(Error(kinds1 intersect kinds2)), nstore))
              }
          }
        case _ => throw NonNormalFormMemories
      })

    override def <=(a1: TypeMemories[T], a2: TypeMemories[T]): Boolean = a1.memories.forall(tymem1 => tymem1.result match {
      case SuccessResult(t1) =>
        a2.memories.exists(tymem2 => tymem2.result match {
          case SuccessResult(t2) =>
            RSLattice[T, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, t1, t2) &&
              RSLattice[TypeStore, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, tymem1.store, tymem2.store)
          case _ => false
        })
      case ExceptionalResult(exres) =>
        exres match {
          case Return(vrt1) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Return(vrt2)) =>
                RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, vrt1, vrt2) &&
                  RSLattice[TypeStore, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, tymem1.store, tymem2.store)
              case _ => false
            })
          case Throw(vrt1) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Throw(vrt2)) =>
                RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, vrt1, vrt2) &&
                  RSLattice[TypeStore, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, tymem1.store, tymem2.store)
              case _ => false
            })
          case Break =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Break) =>
                RSLattice[TypeStore, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, tymem1.store, tymem2.store)
              case _ => false
            })
          case Continue =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Continue) =>
                RSLattice[TypeStore, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, tymem1.store, tymem2.store)
              case _ => false
            })
          case Fail =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Fail) =>
                RSLattice[TypeStore, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, tymem1.store, tymem2.store)
              case _ => false
            })
          case Error(_) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Error(_)) =>
                RSLattice[TypeStore, DataTypeDefs, RefinementDefs].<=(datatypes, !refinements, tymem1.store, tymem2.store)
              case _ => false
            })
        }
    })

    override def widen(a1: TypeMemories[T], a2: TypeMemories[T], depth: Int): TypeMemories[T] =
      upperBound(a1, a2, RSLattice[TypeStore, DataTypeDefs, RefinementDefs].widen(_,_,_,_,depth),
        RSLattice[T, DataTypeDefs, RefinementDefs].widen(_,_,_,_,depth),
        RSLattice[VoideableRefinementType, DataTypeDefs, RefinementDefs].widen(_,_,_,_,depth))
  }
}