package semantics.domains.abstracting

import semantics.Result
import semantics.domains.common.Product._
import semantics.domains.common._
import syntax.VarName
import Relational._
import semantics.domains.abstracting.Memory.{AMemory, AResult, AValue}
import semantics.domains.abstracting.ValueShape.ValueShape

import scalaz.\/

object Memory {
  type AValue = (ValueShape, Flat[VarName \/ RelCt])
  type AResult[T] = ResultV[AValue, T]

  type AMemory[T] = (AResult[T], ACStore)
}

case object NonNormalFormMemories extends Exception

sealed trait AStore
case object StoreTop extends AStore
case class AbstractStore(store: Map[VarName, AValue]) extends AStore

case class ACStore(store: AStore, path: RelCt)

case class AMemories[T](memories: Set[AMemory[T]])


case class MemoryOf(module: Module) {
  val ValueShape = ValueShapeOf(module)

  import ValueShape._

  implicit def AStoreLattice : Lattice[AStore] = new Lattice[AStore] {
    override def <=(a1: AStore, a2: AStore): Boolean = (a1, a2) match {
      case (_, StoreTop) => true
      case (AbstractStore(store1), AbstractStore(store2)) =>
        (store1.keySet subsetOf store2.keySet) && store1.keySet.forall { vari =>
          val (vs1, relcmp1) = store1(vari)
          val (vs2, relcmp2) = store2(vari)
          Lattice[ValueShape].<=(vs1, vs2) && Lattice[Flat[VarName \/ RelCt]].<=(relcmp1, relcmp2)
        }
      case _ => false
    }

    override def widen(a1: AStore, a2: AStore, depth: Int): AStore = upperBound(a1, a2) { (v1, v2) =>
      (v1, v2) match {
        case ((vs1, relcmp1), (vs2, relcmp2)) => (Lattice[ValueShape].widen(vs1, vs2, depth),
          Lattice[Flat[VarName \/ RelCt]].widen(relcmp1, relcmp2, depth))
      }
    }

    override def bot: AStore = AbstractStore(Map.empty)

    override def top: AStore = StoreTop

    override def lub(a1: AStore, a2: AStore): AStore = upperBound(a1, a2) { (v1, v2) =>
      (v1, v2) match {
        case ((vs1, relcmp1), (vs2, relcmp2)) =>
          (Lattice[ValueShape].lub(vs1, vs2), Lattice[Flat[VarName \/ RelCt]].lub(relcmp1, relcmp2))
      }
    }

    private def upperBound(a1: AStore, a2: AStore)(vlub: (AValue, AValue) => AValue) = {
      (a1, a2) match {
        case (StoreTop, _) | (_, StoreTop) => StoreTop
        case (AbstractStore(store1), AbstractStore(store2)) =>
          AbstractStore((store1.keySet union store2.keySet).toList.map { vari =>
            val v1 = store1.get(vari).fold((Lattice[ValueShape].bot, Lattice[Flat[VarName \/ RelCt]].bot))(identity)
            val v2 = store2.get(vari).fold((Lattice[ValueShape].bot, Lattice[Flat[VarName \/ RelCt]].bot))(identity)
            vari -> vlub(v1, v2)
          }.toMap)
      }
    }

    override def glb(a1: AStore, a2: AStore): AStore = {
      (a1, a2) match {
        case (StoreTop, a) => a
        case (a, StoreTop) => a
        case (AbstractStore(store1), AbstractStore(store2)) =>
          AbstractStore((store1.keySet intersect store2.keySet).toList.map { vari =>
            val (vs1, relcmp1) = store1(vari)
            val (vs2, relcmp2) = store2(vari)
            vari -> (Lattice[ValueShape].glb(vs1, vs2), Lattice[Flat[VarName \/ RelCt]].glb(relcmp1, relcmp2))
          }.toMap)
      }
    }
  }

  implicit def AMemoriesLattice[E : Lattice] : Lattice[AMemories[E]] = new Lattice[AMemories[E]] {
    override def bot: AMemories[E] = AMemories(Set())

    override def top: AMemories[E] = {
      val valtop = Lattice[AValue].top
      AMemories(Set(
        SuccessResult(Lattice[E].top)
        , ExceptionalResult(Return(valtop))
        , ExceptionalResult(Throw(valtop))
        , ExceptionalResult(Break)
        , ExceptionalResult(Continue)
        , ExceptionalResult(Fail)
        , ExceptionalResult(Error(OtherError))
      ).map(res => (res, ACStore(Lattice[AStore].top, Lattice[RelCt].top))))
    }

    override def lub(a1: AMemories[E], a2: AMemories[E]): AMemories[E] =
      upperBound(a1, a2)(Lattice[AValue].lub)(Lattice[E].lub)

    private def upperBound(a1: AMemories[E], a2: AMemories[E])(vlub: (AValue, AValue) => AValue)(elub: (E,E) => E) = {
      val grouped: Map[ResultV[Unit, Unit], Set[AMemory[E]]] = groupMemories(a1, a2)
      AMemories(grouped.values.toSet[Set[AMemory[E]]].flatMap[AMemory[E], Set[AMemory[E]]] { ress =>
        if (ress.size <= 1) ress
        else if (ress.size == 2) {
          ress.toList match {
            case List((res1, ACStore(store1, rel1)), (res2, ACStore(store2, rel2))) =>
              val nres = res1 match {
                case SuccessResult(value1) =>
                  val SuccessResult(value2) = res2
                  SuccessResult(elub(value1, value2))
                case ExceptionalResult(exres) =>
                  exres match {
                    case Return(value1) =>
                      val ExceptionalResult(Return(value2)) = res2
                      ExceptionalResult(Return(vlub(value1,value2)))
                    case Throw(value1) =>
                      val ExceptionalResult(Throw(value2)) = res2
                      ExceptionalResult(Throw(vlub(value1,value2)))
                    case Break => ExceptionalResult(Break)
                    case Continue => ExceptionalResult(Continue)
                    case Fail => ExceptionalResult(Fail)
                    case Error(kind) => ExceptionalResult(Error(OtherError))
                  }
              }
              val nstore = Lattice[AStore].lub(store1, store2)
              val nrel = Lattice[RelCt].lub(rel1, rel2)
              Set((nres, ACStore(nstore, nrel)))
          }
        }
        else throw NonNormalFormMemories
      })
    }

    private
    def groupMemories(a1: AMemories[E], a2: AMemories[E]) = {
      val grouped = (a1.memories union a2.memories).groupBy[ResultV[Unit, Unit]] {
        _._1 match {
          case SuccessResult(t) => SuccessResult(())
          case ExceptionalResult(exres) =>
            ExceptionalResult(exres match {
              case Return(_) => Return(())
              case Throw(_) => Throw(())
              case Break => Break
              case Continue => Continue
              case Fail => Fail
              case Error(_) => Error(OtherError)
            })
        }
      }
      grouped
    }

    override def glb(a1: AMemories[E], a2: AMemories[E]): AMemories[E] = {
      val grouped: Map[ResultV[Unit, Unit], Set[AMemory[E]]] = groupMemories(a1, a2)
      AMemories(grouped.values.toSet[Set[AMemory[E]]].flatMap[AMemory[E], Set[AMemory[E]]] { ress =>
        if (ress.size <= 1) Set()
        else if (ress.size == 2) {
          ress.toList match {
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
                    case Error(kind) => ExceptionalResult(Error(OtherError))
                  }
              }
              val nstore = Lattice[AStore].lub(store1, store2)
              val nrel = Lattice[RelCt].lub(rel1, rel2)
              Set((nres, ACStore(nstore, nrel)))
          }
        }
        else throw NonNormalFormMemories
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
