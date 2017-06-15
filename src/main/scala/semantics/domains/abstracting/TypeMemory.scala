package semantics.domains.abstracting

import semantics.domains.abstracting.TypeMemory.{TypeResult}
import semantics.domains.common._
import syntax.{Type, VarName}
import semantics.domains.concrete.TypeOps._

sealed trait TypeStore
case object TypeStoreTop extends TypeStore
case class TypeStoreV(vals: Map[VarName, (Boolean, Type)]) extends TypeStore

case class TypeMemory[T](result: TypeResult[T], store: TypeStore)
case class TypeMemories[T](memories: Set[TypeMemory[T]])

object TypeMemory {
  type TypeResult[T] = ResultV[Type, T]

  implicit def TypeStoreLattice = new Lattice[TypeStore] {
    override def bot: TypeStore = TypeStoreV(Map())

    override def top: TypeStore = TypeStoreTop

    private def upperBound(a1: TypeStore, a2: TypeStore, tOp : (Type, Type) => Type) = {
      (a1, a2) match {
        case (TypeStoreTop, _) | (_, TypeStoreTop) => TypeStoreTop
        case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
          val allVars = vals1.keySet ++ vals2.keySet
          TypeStoreV(allVars.map { x =>
            vals1.get(x).fold(x -> (true, vals2(x)._2)) { case (pu1, ty1) =>
              vals2.get(x).fold(x -> (true, ty1)) { case (pu2, ty2) =>
                x -> (pu1 || pu2, tOp(ty1, ty2))
              }
            }
          }.toMap)
      }
    }

    override def lub(a1: TypeStore, a2: TypeStore): TypeStore = upperBound(a1, a2, Lattice[Type].lub)

    override def glb(a1: TypeStore, a2: TypeStore): TypeStore = {
      (a1, a2) match {
        case (TypeStoreTop, _) => a2
        case (_, TypeStoreTop) => a1
        case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
          val sharedVars = vals1.keySet intersect vals2.keySet
          TypeStoreV(sharedVars.map { x =>
            val (pu1, ty1) = vals1(x)
            val (pu2, ty2) = vals2(x)
            x -> (pu1 && pu2, Lattice[Type].glb(ty1, ty2))
          }.toMap)
      }
    }

    override def <=(a1: TypeStore, a2: TypeStore): Boolean = (a1, a2) match {
      case (_, TypeStoreTop) => true
      case (TypeStoreV(vals1), TypeStoreV(vals2)) =>
        vals1.keySet.forall { x =>
          val (pu1, ty1) = vals1(x)
          vals2.get(x).fold(false) { case (pu2, ty2) =>
              pu1 <= pu2 && Lattice[Type].<=(ty1, ty2)
          }
        }
      case _ => false
    }

    override def widen(a1: TypeStore, a2: TypeStore, depth: Int): TypeStore =
      upperBound(a1, a2, Lattice[Type].widen(_, _, depth))
  }

  implicit def TypeMemoriesLattice[T : Lattice] = new Lattice[TypeMemories[T]] {
    override def bot: TypeMemories[T] = TypeMemories(Set())

    override def top: TypeMemories[T] =
    TypeMemories(
      Set(TypeMemory(SuccessResult(Lattice[T].top), Lattice[TypeStore].top)
       , TypeMemory(ExceptionalResult(Return(Lattice[Type].top)), Lattice[TypeStore].top)
       , TypeMemory(ExceptionalResult(Throw(Lattice[Type].top)), Lattice[TypeStore].top)
       , TypeMemory(ExceptionalResult(Break), Lattice[TypeStore].top)
       , TypeMemory(ExceptionalResult(Continue), Lattice[TypeStore].top)
       , TypeMemory(ExceptionalResult(Fail), Lattice[TypeStore].top)
       , TypeMemory(ExceptionalResult(Error(OtherError)), Lattice[TypeStore].top)
    ))

    private
    def groupMemories(a1: TypeMemories[T], a2: TypeMemories[T]): Set[List[TypeMemory[T]]] = {
      val grouped = (a1.memories.toList ++ a2.memories.toList).groupBy[String] {
        _.result match {
          case SuccessResult(t) => "SuccessResult"
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

    override def lub(a1: TypeMemories[T], a2: TypeMemories[T]): TypeMemories[T] =
    {
      TypeMemories(groupMemories(a1, a2).flatMap[TypeMemory[T], Set[TypeMemory[T]]] {
        case ress@(List() | List(_)) => ress
        case List(tmem1, tmem2) =>
          val nres = tmem1.result match {
            case SuccessResult(t1) =>
              val SuccessResult(t2) = tmem2.result
              SuccessResult(Lattice[T].lub(t1, t2))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(ty1) =>
                  val ExceptionalResult(Return(ty2)) = tmem2.result
                  ExceptionalResult(Return(Lattice[Type].lub(ty1, ty2)))
                case Throw(ty1) =>
                  val ExceptionalResult(Throw(ty2)) = tmem2.result
                  ExceptionalResult(Throw(Lattice[Type].lub(ty1, ty2)))
                case Break => ExceptionalResult(Break)
                case Continue => ExceptionalResult(Continue)
                case Fail => ExceptionalResult(Fail)
                case Error(kind) => ExceptionalResult(Error(OtherError))
              }
          }
          val nstore = Lattice[TypeStore].lub(tmem1.store, tmem2.store)
          Set(TypeMemory(nres, nstore))
        case _ => throw NonNormalFormMemories
      })
    }

    override def glb(a1: TypeMemories[T], a2: TypeMemories[T]): TypeMemories[T] =
      TypeMemories(groupMemories(a1, a2).flatMap[TypeMemory[T], Set[TypeMemory[T]]] {
        case List() | List(_) => Set()
        case List(tmem1, tmem2) =>
          val nres: TypeResult[T] = tmem1.result match {
            case SuccessResult(t1) =>
              val SuccessResult(t2) = tmem2.result
              SuccessResult(Lattice[T].glb(t1, t2))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(ty1) =>
                  val ExceptionalResult(Return(ty2)) = tmem2.result
                  ExceptionalResult(Return(Lattice[Type].lub(ty1, ty2)))
                case Throw(ty1) =>
                  val ExceptionalResult(Throw(ty2)) = tmem2.result
                  ExceptionalResult(Throw(Lattice[Type].lub(ty1, ty2)))
                case Break => ExceptionalResult(Break)
                case Continue => ExceptionalResult(Continue)
                case Fail => ExceptionalResult(Fail)
                case Error(kind) => ExceptionalResult(Error(OtherError))
              }
          }
          val nstore = Lattice[TypeStore].lub(tmem1.store, tmem2.store)
          Set(TypeMemory(nres, nstore))
        case _ => throw NonNormalFormMemories
      })

    override def <=(a1: TypeMemories[T], a2: TypeMemories[T]): Boolean = a1.memories.forall(tymem1 => tymem1.result match {
      case SuccessResult(t1) =>
        a2.memories.exists(tymem2 => tymem2.result match {
          case SuccessResult(t2) => Lattice[T].<=(t1, t2) && Lattice[TypeStore].<=(tymem1.store, tymem2.store)
          case _ => false
        })
      case ExceptionalResult(exres) =>
        exres match {
          case Return(t1) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Return(t2)) => Lattice[Type].<=(t1, t2) && Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
              })
          case Throw(t1) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Throw(t2)) => Lattice[Type].<=(t1, t2) && Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Break =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Break) => Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Continue =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Continue) => Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Fail =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Fail) => Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
          case Error(_) =>
            a2.memories.exists(tymem2 => tymem2.result match {
              case ExceptionalResult(Error(_)) => Lattice[TypeStore].<=(tymem1.store, tymem2.store)
              case _ => false
            })
        }
    })

    override def widen(a1: TypeMemories[T], a2: TypeMemories[T], depth: Int): TypeMemories[T] = lub(a1, a2)
  }
}