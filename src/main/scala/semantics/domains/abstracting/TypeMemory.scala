package semantics.domains.abstracting

import semantics.domains.abstracting.RefinementTypes._
import semantics.domains.abstracting.TypeStore.TypeResult
import semantics.domains.common._
import syntax.VarName

sealed trait TypeStore
case object TypeStoreTop extends TypeStore
case class TypeStoreV(vals: Map[VarName, VoideableRefinementType]) extends TypeStore
case object TypeStoreBot extends TypeStore

case class TypeMemory[T](result: TypeResult[T], store: TypeStore)
case class TypeMemories[T](memories: Set[TypeMemory[T]])

object TypeStore {
  type TypeResult[T] = ResultV[VoideableRefinementType, T]
}

case class TypeStoreOps(datatypes: DataTypeDefs, refinements: Refinements) {

  private
  val refinementTypeOps = RefinementTypeOps(datatypes, refinements)

  import refinementTypeOps._

  def getVar(store: TypeStore, x: VarName): Option[VoideableRefinementType] = store match {
    case TypeStoreBot => None
    case TypeStoreV(storemap) => storemap.get(x)
    case TypeStoreTop => Some(Lattice[VoideableRefinementType].top)
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

  implicit def TypeStoreLattice = new Lattice[TypeStore] {
    override def bot: TypeStore = TypeStoreBot

    override def top: TypeStore = TypeStoreTop

    private def upperBound(store1: TypeStore, store2: TypeStore,
                           tOp : (VoideableRefinementType, VoideableRefinementType) => VoideableRefinementType): TypeStore = {
      (store1, store2) match {
        case (TypeStoreTop, _) | (_, TypeStoreTop) => TypeStoreTop
        case (TypeStoreBot, _) => store2
        case (_, TypeStoreBot) => store1
        case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
          val allVars = vals1.keySet ++ vals2.keySet
          val varmap = allVars.foldLeft( Map.empty[VarName, VoideableRefinementType]) { (prevvarmap, x) =>
            vals1.get(x).fold(prevvarmap.updated(x, VoideableRefinementType(possiblyVoid = true, vals2(x).refinementType))) { vty1 =>
              vals2.get(x).fold(prevvarmap.updated(x, VoideableRefinementType(possiblyVoid = true, vty1.refinementType))) { vty2 =>
                val newrefinetyp = tOp(vty1, vty2)
                prevvarmap.updated(x, newrefinetyp)
              }
            }
          }
          TypeStoreV(varmap)
      }
    }

    override def lub(store1: TypeStore, store2: TypeStore): TypeStore = {
      upperBound(store1, store2, Lattice[VoideableRefinementType].lub)
    }

    override def glb(store1: TypeStore, store2: TypeStore): TypeStore = {
      (store1, store2) match {
        case (TypeStoreBot, _) | (_, TypeStoreBot) => TypeStoreBot
        case (TypeStoreTop, _) => store2
        case (_, TypeStoreTop) => store1
        case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
          val sharedVars = vals1.keySet intersect vals2.keySet
          val varmap = sharedVars.foldLeft(Map.empty[VarName, VoideableRefinementType]) { (prevvarmap, x) =>
            val vty1 = vals1(x)
            val vty2 = vals2(x)
            val newrefinetyp = Lattice[VoideableRefinementType].glb(vty1, vty2)
            prevvarmap.updated(x, newrefinetyp)
          }
          TypeStoreV(varmap)
      }
    }

    override def <=(store1: TypeStore, store2: TypeStore): Boolean = (store1, store2) match {
      case (_, TypeStoreTop) => true
      case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
        vals1.keySet.forall { x =>
          val vty1 = vals1(x)
          vals2.get(x).fold(false)(vty2 => Lattice[VoideableRefinementType].<=(vty1, vty2))
        }
      case _ => false
    }

    override def widen(store1: TypeStore, store2: TypeStore, bound: Int): TypeStore =
      upperBound(store1, store2, Lattice[VoideableRefinementType].widen(_, _, bound))
  }

}

case class TypeMemoriesOps(module: Module, refinements: Refinements) {
  val datatypes: DataTypeDefs = module.datatypes.mapValues(conss => module.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))

  val typestoreops = TypeStoreOps(datatypes, refinements)
  import typestoreops._

  val refinementtypeops = RefinementTypeOps(datatypes, refinements)
  import refinementtypeops._

  implicit def TypeMemoriesLatticeFromRS[T](implicit lattt: Lattice[T]) = new Lattice[TypeMemories[T]] {
    override def bot: TypeMemories[T] = TypeMemories(Set())

    override def top: TypeMemories[T] = {
      val topstore = Lattice[TypeStore].top
      TypeMemories(
        Set(TypeMemory(SuccessResult(Lattice[T].top), topstore)
          , TypeMemory(ExceptionalResult(Return(Lattice[VoideableRefinementType].top)), topstore)
          , TypeMemory(ExceptionalResult(Throw(Lattice[VoideableRefinementType].top)), topstore)
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
                            storeOp: (TypeStore, TypeStore) => TypeStore, tOp: (T, T) => T,
                            vrtOp: (VoideableRefinementType, VoideableRefinementType) => VoideableRefinementType): TypeMemories[T] =
    {
      TypeMemories(groupMemories(a1, a2).flatMap[TypeMemory[T], Set[TypeMemory[T]]] {
        case ress@(List() | List(_)) => ress.toSet[TypeMemory[T]]
        case List(tmem1, tmem2) =>
          val nstore = storeOp(tmem1.store, tmem2.store)
          tmem1.result match {
            case SuccessResult(t1) =>
              val SuccessResult(t2) = tmem2.result
              val tlub = tOp(t1, t2)
              Set(TypeMemory[T](SuccessResult(tlub), nstore))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(vrty1) =>
                  val ExceptionalResult(Return(vrty2)) = tmem2.result
                  val vrtylub = vrtOp(vrty1, vrty2)
                  Set(TypeMemory[T](ExceptionalResult(Return(vrtylub)), nstore))
                case Throw(vrty1) =>
                  val ExceptionalResult(Throw(vrty2)) = tmem2.result
                  val vrtylub = vrtOp(vrty1, vrty2)
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
      upperBound(a1, a2, Lattice[TypeStore].lub,
        Lattice[T].lub, Lattice[VoideableRefinementType].lub)

    override def glb(a1: TypeMemories[T], a2: TypeMemories[T]): TypeMemories[T] =
      TypeMemories(groupMemories(a1, a2).flatMap[TypeMemory[T], Set[TypeMemory[T]]] {
        case List() | List(_) => Set()
        case List(tmem1, tmem2) =>
          val nstore = Lattice[TypeStore].glb(tmem1.store, tmem2.store)
          tmem1.result match {
            case SuccessResult(t1) =>
              val SuccessResult(t2) = tmem2.result
              val tglb = Lattice[T].glb(t1, t2)
              Set(TypeMemory[T](SuccessResult(tglb), nstore))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(vrt1) =>
                  val ExceptionalResult(Return(vrt2)) = tmem2.result
                  val vrtglb = Lattice[VoideableRefinementType].glb(vrt1, vrt2)
                  Set(TypeMemory[T](ExceptionalResult(Return(vrtglb)), nstore))
                case Throw(vrt1) =>
                  val ExceptionalResult(Throw(vrt2)) = tmem2.result
                  val vrtglb = Lattice[VoideableRefinementType].glb(vrt1, vrt2)
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
            Lattice[T].<=(t1, t2) && Lattice[TypeStore].<=(tymem1.store, tymem2.store)
          case _ => false
        })
      case ExceptionalResult(exres) =>
        exres match {
          case Return(vrt1) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Return(vrt2)) =>
                Lattice[VoideableRefinementType].<=(vrt1, vrt2) &&
                  Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Throw(vrt1) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Throw(vrt2)) =>
                Lattice[VoideableRefinementType].<=(vrt1, vrt2) &&
                  Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Break =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Break) =>
                Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Continue =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Continue) =>
                Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Fail =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Fail) =>
                Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Error(_) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Error(_)) =>
                Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
        }
    })

    override def widen(a1: TypeMemories[T], a2: TypeMemories[T], depth: Int): TypeMemories[T] =
      upperBound(a1, a2, Lattice[TypeStore].widen(_,_,depth),
        Lattice[T].widen(_,_,depth),
        Lattice[VoideableRefinementType].widen(_,_,depth))
  }
}