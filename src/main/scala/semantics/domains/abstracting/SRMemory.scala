package semantics.domains.abstracting

import semantics.domains.abstracting.Relational._
import semantics.domains.abstracting.ValueShape.ValueShape
import semantics.domains.common.Flat._
import semantics.domains.common.Product._
import semantics.domains.common._
import syntax.VarName

import scalaz.\/

object SRMemory {
  type AValue = (ValueShape, Flat[VarName \/ RelCt])
  type AResult[T] = ResultV[AValue, T]
  type AStore = Flat[Map[VarName, AValue]]
  type AMemory[T] = (AResult[T], ACStore)
}

import SRMemory._

case object NonNormalFormMemories extends Exception

case class ACStore(store: AStore, path: RelCt)

case class AMemories[T](memories: Set[AMemory[T]])


case class SRMemoryOf(module: Module) {
  val ValueShape = ValueShapeOf(module)

  import ValueShape._

  implicit def AMemoriesLattice[E : Lattice] : Lattice[AMemories[E]] = new Lattice[AMemories[E]] {
    override def bot: AMemories[E] = AMemories(Set())

    override def top: AMemories[E] = {
      val valtop = Lattice[AValue].top
      AMemories[E](Set(
        SuccessResult(Lattice[E].top)
        , ExceptionalResult(Return(valtop))
        , ExceptionalResult(Throw(valtop))
        , ExceptionalResult(Break)
        , ExceptionalResult(Continue)
        , ExceptionalResult(Fail)
        , ExceptionalResult(Error(Set(OtherError)))
      ).map(res => (res, ACStore(Lattice[AStore].top, Lattice[RelCt].top))))
    }

    override def lub(a1: AMemories[E], a2: AMemories[E]): AMemories[E] =
      upperBound(a1, a2)(Lattice[AValue].lub)(Lattice[E].lub)

    private def upperBound(a1: AMemories[E], a2: AMemories[E])(vlub: (AValue, AValue) => AValue)(elub: (E,E) => E) = {
      val grouped: Set[List[AMemory[E]]] = groupMemories(a1, a2)
      AMemories(grouped.flatMap[AMemory[E], Set[AMemory[E]]] {
        case ress@(List() | List(_)) => ress
        case List((res1, ACStore(store1, rel1)), (res2, ACStore(store2, rel2))) =>
          val nres = res1 match {
            case SuccessResult(value1) =>
              val SuccessResult(value2) = res2
              SuccessResult(elub(value1, value2))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(value1) =>
                  val ExceptionalResult(Return(value2)) = res2
                  ExceptionalResult(Return(vlub(value1, value2)))
                case Throw(value1) =>
                  val ExceptionalResult(Throw(value2)) = res2
                  ExceptionalResult(Throw(vlub(value1, value2)))
                case Break => ExceptionalResult(Break)
                case Continue => ExceptionalResult(Continue)
                case Fail => ExceptionalResult(Fail)
                case Error(kinds1) =>
                  val ExceptionalResult(Error(kinds2)) = res2
                  ExceptionalResult(Error(kinds1 union kinds2))
              }
          }
          val nstore = Lattice[AStore].lub(store1, store2)
          val nrel = Lattice[RelCt].lub(rel1, rel2)
          Set((nres, ACStore(nstore, nrel)))
        case _ => throw NonNormalFormMemories
      })
    }

    private
    def groupMemories(a1: AMemories[E], a2: AMemories[E]): Set[List[AMemory[E]]] = {
      val grouped = (a1.memories.toList ++ a2.memories.toList).groupBy[String] {
        _._1 match {
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

    override def glb(a1: AMemories[E], a2: AMemories[E]): AMemories[E] = {
      val grouped: Set[List[AMemory[E]]] = groupMemories(a1, a2)
      AMemories(grouped.flatMap[AMemory[E], Set[AMemory[E]]] {
        case List() | List(_) => Set()
        case List((res1, ACStore(store1, rel1)), (res2, ACStore(store2, rel2))) =>
          val nres = res1 match {
            case SuccessResult(val1) =>
              val SuccessResult(val2) = res2
              SuccessResult(Lattice[E].glb(val1, val2))
            case ExceptionalResult(exres) =>
              exres match {
                case Return(val1) =>
                  val ExceptionalResult(Return(val2)) = res2
                  ExceptionalResult(Return(Lattice[AValue].lub(val1, val2)))
                case Throw(val1) =>
                  val ExceptionalResult(Throw(val2)) = res2
                  ExceptionalResult(Throw(Lattice[AValue].lub(val1, val2)))
                case Break => ExceptionalResult(Break)
                case Continue => ExceptionalResult(Continue)
                case Fail => ExceptionalResult(Fail)
                case Error(kinds1) =>
                  val ExceptionalResult(Error(kinds2)) = res2
                  ExceptionalResult(Error(kinds1 intersect kinds2))
              }
          }
          val nstore = Lattice[AStore].lub(store1, store2)
          val nrel = Lattice[RelCt].lub(rel1, rel2)
          Set((nres, ACStore(nstore, nrel)))
        case _ => throw NonNormalFormMemories
      })
    }

    override def <=(a1: AMemories[E], a2: AMemories[E]): Boolean = a1.memories.forall {
      case (res1, ACStore(store1, rel1)) =>
        res1 match {
          case SuccessResult(val1) =>
            a2.memories.exists { case (res2, ACStore(store2, rel2)) =>
              res2 match {
                case SuccessResult(val2) =>
                  Lattice[E].<=(val1,val2) &&
                  Lattice[AStore].<=(store1, store2) &&
                  Lattice[RelCt].<=(rel1, rel2)
                case _ => false
              }
            }
          case ExceptionalResult(exres) =>
            exres match {
              case Return(val1) =>
                a2.memories.exists { case (res2, ACStore(store2, rel2)) =>
                  res2 match {
                    case (ExceptionalResult(Return(val2))) =>
                      Lattice[AValue].<=(val1, val2)
                    case _ => false
                  }
                }
              case Throw(val1) =>
                a2.memories.exists { case (res2, ACStore(store2, rel2)) =>
                  res2 match {
                    case (ExceptionalResult(Throw(val2))) =>
                      Lattice[AValue].<=(val1, val2) &&
                        Lattice[AStore].<=(store1, store2) &&
                        Lattice[RelCt].<=(rel1, rel2)
                    case _ => false
                  }
                }
              case Break =>
                a2.memories.exists { case (res2, ACStore(store2, rel2)) =>
                  res2 match {
                    case (ExceptionalResult(Break)) =>
                        Lattice[AStore].<=(store1, store2) &&
                        Lattice[RelCt].<=(rel1, rel2)
                    case _ => false
                  }
                }
              case Continue =>
                a2.memories.exists { case (res2, ACStore(store2, rel2)) =>
                  res2 match {
                    case (ExceptionalResult(Continue)) =>
                      Lattice[AStore].<=(store1, store2) &&
                        Lattice[RelCt].<=(rel1, rel2)
                    case _ => false
                  }
                }
              case Fail =>
                a2.memories.exists { case (res2, ACStore(store2, rel2)) =>
                  res2 match {
                    case (ExceptionalResult(Fail)) =>
                      Lattice[AStore].<=(store1, store2) &&
                        Lattice[RelCt].<=(rel1, rel2)
                    case _ => false
                  }
                }
              case Error(kind) =>
                a2.memories.exists { case (res2, ACStore(store2, rel2)) =>
                  res2 match {
                    case (ExceptionalResult(Error(_))) =>
                      Lattice[AStore].<=(store1, store2) &&
                        Lattice[RelCt].<=(rel1, rel2)
                    case _ => false
                  }
                }
            }
        }
    }

    override def widen(a1: AMemories[E], a2: AMemories[E], depth: Int): AMemories[E] =
      upperBound(a1, a2)(Lattice[AValue].widen(_, _,depth))(Lattice[E].widen(_, _, depth))
  }
}
