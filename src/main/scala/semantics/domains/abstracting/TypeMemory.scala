package semantics.domains.abstracting

import semantics.domains.abstracting.RefinementTypes._
import semantics.domains.abstracting.TypeStore.TypeResult
import semantics.domains.common._
import syntax.VarName

sealed trait TypeStore
case object TypeStoreTop extends TypeStore
case class TypeStoreV(vals: Map[VarName, VoideableRefinementType]) extends TypeStore
case object TypeStoreBot extends TypeStore

case class TypeMemory[T,F](result: TypeResult[T,F], store: TypeStore)
case class TypeMemories[T,F](memories: Set[TypeMemory[T,F]])

object TypeResult {
  def pretty(typeResult: TypeResult[VoideableRefinementType, Unit]): String = typeResult match {
    case SuccessResult(t) =>
      s"success ${VoideableRefinementTypes.pretty(t)}"
    case ExceptionalResult(exres) =>
      exres match {
        case Return(value) => s"return ${VoideableRefinementTypes.pretty(value)}"
        case Throw(value) => s"throw ${VoideableRefinementTypes.pretty(value)}"
        case Break => "break"
        case Continue => "continue"
        case Fail(_) => s"fail"
        case Error(kinds) =>
          s"errors: \n ${kinds.map(errk => "\t" + errk).mkString("\n")}"
      }
  }
}

object TypeStore {
  def pretty(store: TypeStore): VarName = store match {
    case TypeStoreTop => "store⊤"
    case TypeStoreV(vals) => vals.map { case (vr, vl) => s"$vr ↦ ${VoideableRefinementTypes.pretty(vl)}" }.mkString("[", ",", "]")
    case TypeStoreBot => "store⊥"
  }

  type TypeResult[T, F] = ResultV[VoideableRefinementType, T, F]
}

object TypeMemory {
  def pretty(mem: TypeMemory[VoideableRefinementType, Unit]): String = {
    val prettyRes = TypeResult.pretty(mem.result)
    val prettyStore = TypeStore.pretty(mem.store)
    s"""result:
       | $prettyRes
       |
       |store:
       | $prettyStore""".stripMargin
  }
}

object TypeMemories {
  def pretty(mems: TypeMemories[VoideableRefinementType, Unit]): String = {
    mems.memories.map(TypeMemory.pretty).mkString("\n")
  }
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

  implicit def TypeStoreLattice: Lattice[TypeStore] = new Lattice[TypeStore] {
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
            vals1.get(x).fold {
              val v2rty = vals2(x)
              if (Lattice[VoideableRefinementType].isBot(v2rty)) prevvarmap
              else prevvarmap.updated(x, VoideableRefinementType(possiblyVoid = true, v2rty.refinementType))
            } { vty1 =>
              vals2.get(x).fold {
                if (Lattice[VoideableRefinementType].isBot(vty1)) prevvarmap
                else prevvarmap.updated(x, VoideableRefinementType(possiblyVoid = true, vty1.refinementType))
              } { vty2 =>
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
  val datatypes: DataTypeDefs =
    module.datatypes.mapValues(conss => module.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))

  val typestoreops = TypeStoreOps(datatypes, refinements)
  import typestoreops._

  val refinementtypeops = RefinementTypeOps(datatypes, refinements)
  import refinementtypeops._

  implicit def TypeMemoriesLatticeFromRS[T,F](implicit lattt: Lattice[T], lattf: Lattice[F]): Lattice[TypeMemories[T, F]] = new Lattice[TypeMemories[T,F]] {
    override def bot: TypeMemories[T,F] = TypeMemories(Set())

    override def top: TypeMemories[T,F] = {
      val topstore = Lattice[TypeStore].top
      TypeMemories(
        Set(TypeMemory(SuccessResult(Lattice[T].top), topstore)
          , TypeMemory(ExceptionalResult(Return(Lattice[VoideableRefinementType].top)), topstore)
          , TypeMemory(ExceptionalResult(Throw(Lattice[VoideableRefinementType].top)), topstore)
          , TypeMemory(ExceptionalResult(Break), topstore)
          , TypeMemory(ExceptionalResult(Continue), topstore)
          , TypeMemory(ExceptionalResult(Fail(Lattice[F].top)), topstore)
          , TypeMemory(ExceptionalResult(Error(Set(OtherError))), topstore)
        ))
    }

    private
    def groupMemories(a1: TypeMemories[T,F], a2: TypeMemories[T,F]): Set[List[TypeMemory[T,F]]] = {
      val grouped = (a1.memories.toList ++ a2.memories.toList).groupBy[String](_.result.kind)
      grouped.values.toSet
    }

    private
    def upperBound(a1: TypeMemories[T,F], a2: TypeMemories[T,F],
                            storeOp: (TypeStore, TypeStore) => TypeStore, tOp: (T, T) => T, fOp: (F, F) => F,
                            vrtOp: (VoideableRefinementType, VoideableRefinementType) => VoideableRefinementType): TypeMemories[T,F] =
    {
      TypeMemories(groupMemories(a1, a2).flatMap[TypeMemory[T,F], Set[TypeMemory[T,F]]] {
        case ress@(List() | List(_)) => ress.toSet[TypeMemory[T,F]]
        case List(tmem1, tmem2) =>
          val nstore = storeOp(tmem1.store, tmem2.store)
          tmem1.result match {
            case SuccessResult(t1) =>
              val SuccessResult(t2) = tmem2.result
              val tlub = tOp(t1, t2)
              Set(TypeMemory[T,F](SuccessResult(tlub), nstore))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(vrty1) =>
                  val ExceptionalResult(Return(vrty2)) = tmem2.result
                  val vrtylub = vrtOp(vrty1, vrty2)
                  Set(TypeMemory[T,F](ExceptionalResult(Return(vrtylub)), nstore))
                case Throw(vrty1) =>
                  val ExceptionalResult(Throw(vrty2)) = tmem2.result
                  val vrtylub = vrtOp(vrty1, vrty2)
                  Set(TypeMemory[T,F](ExceptionalResult(Throw(vrtylub)), nstore))
                case Break =>
                  Set(TypeMemory[T,F](ExceptionalResult(Break), nstore))
                case Continue =>
                  Set(TypeMemory[T,F](ExceptionalResult(Continue), nstore))
                case Fail(refin1) =>
                  val ExceptionalResult(Fail(refin2)) = tmem2.result
                  val flub = fOp(refin1, refin2)
                  Set(TypeMemory[T,F](ExceptionalResult(Fail(flub)), nstore))
                case Error(kinds1) =>
                  val ExceptionalResult(Error(kinds2)) = tmem2.result
                  Set(TypeMemory[T,F](ExceptionalResult(Error(kinds1 union kinds2)), nstore))
              }
          }
        case _ => throw NonNormalFormMemories
      })
    }

    override def lub(a1: TypeMemories[T,F], a2: TypeMemories[T,F]): TypeMemories[T,F] =
      upperBound(a1, a2, Lattice[TypeStore].lub, Lattice[T].lub, Lattice[F].lub, Lattice[VoideableRefinementType].lub)

    override def glb(a1: TypeMemories[T,F], a2: TypeMemories[T,F]): TypeMemories[T,F] =
      TypeMemories(groupMemories(a1, a2).flatMap[TypeMemory[T,F], Set[TypeMemory[T,F]]] {
        case List() | List(_) => Set()
        case List(tmem1, tmem2) =>
          val nstore = Lattice[TypeStore].glb(tmem1.store, tmem2.store)
          tmem1.result match {
            case SuccessResult(t1) =>
              val SuccessResult(t2) = tmem2.result
              val tglb = Lattice[T].glb(t1, t2)
              Set(TypeMemory[T,F](SuccessResult(tglb), nstore))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(vrt1) =>
                  val ExceptionalResult(Return(vrt2)) = tmem2.result
                  val vrtglb = Lattice[VoideableRefinementType].glb(vrt1, vrt2)
                  Set(TypeMemory[T,F](ExceptionalResult(Return(vrtglb)), nstore))
                case Throw(vrt1) =>
                  val ExceptionalResult(Throw(vrt2)) = tmem2.result
                  val vrtglb = Lattice[VoideableRefinementType].glb(vrt1, vrt2)
                  Set(TypeMemory[T,F](ExceptionalResult(Throw(vrtglb)), nstore))
                case Break => Set(TypeMemory[T,F](ExceptionalResult(Break), nstore))
                case Continue => Set(TypeMemory[T,F](ExceptionalResult(Continue), nstore))
                case Fail(refin1) =>
                  val ExceptionalResult(Fail(refin2)) = tmem2.result
                  val refinglb = Lattice[F].glb(refin1, refin2)
                  Set(TypeMemory[T,F](ExceptionalResult(Fail(refinglb)), nstore))
                case Error(kinds1) =>
                  val ExceptionalResult(Error(kinds2)) = tmem2.result
                  Set(TypeMemory[T,F](ExceptionalResult(Error(kinds1 intersect kinds2)), nstore))
              }
          }
        case _ => throw NonNormalFormMemories
      })

    override def <=(a1: TypeMemories[T,F], a2: TypeMemories[T,F]): Boolean = a1.memories.forall(tymem1 => tymem1.result match {
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
          case Fail(refin1) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Fail(refin2)) =>
                Lattice[F].<=(refin1, refin2) &&
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

    override def widen(a1: TypeMemories[T,F], a2: TypeMemories[T,F], depth: Int): TypeMemories[T,F] =
      upperBound(a1, a2, Lattice[TypeStore].widen(_,_,depth),
        Lattice[T].widen(_,_,depth), Lattice[F].widen(_,_,depth),
        Lattice[VoideableRefinementType].widen(_,_,depth))
  }
}