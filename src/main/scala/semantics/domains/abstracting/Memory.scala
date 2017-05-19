package semantics.domains.abstracting

import semantics.Result
import semantics.domains.common._
import syntax.VarName
import Relational._
import semantics.domains.abstracting.Memory.{AMemory, AValue}
import semantics.domains.abstracting.ValueShape.ValueShape

object Memory {
  type AValue = (ValueShape, Flat[VarName])
  type AResult[T] = ResultV[Unit, T]

  type AMemory = (AResult[AValue], AStore, RelCt)

}

sealed trait AStore
case object StoreTop extends AStore
case class AbstractStore(store: Map[VarName, AValue]) extends AStore

case class AMemories(memories: Set[AMemory])


case class MemoryOf(module: Module) {
  val ValueShape = ValueShapeOf(module)

  import ValueShape._

  implicit def AStoreLattice : Lattice[AStore] = new Lattice[AStore] {
    override def <=(a1: AStore, a2: AStore): Boolean = (a1, a2) match {
      case (_, StoreTop) => true
      case (AbstractStore(store1), AbstractStore(store2)) =>
        (store1.keySet subsetOf store2.keySet) && store1.keySet.forall { vari =>
          val (vs1, sym1) = store1(vari)
          val (vs2, sym2) = store2(vari)
          Lattice[ValueShape].<=(vs1, vs2) && Lattice[Flat[VarName]].<=(sym1, sym2)
        }
      case _ => false
    }

    override def widen(a1: AStore, a2: AStore, depth: Int): AStore = upperBound(a1, a2) { (v1, v2) =>
      (v1, v2) match {
        case ((vs1, sym1), (vs2, sym2)) => (Lattice[ValueShape].widen(vs1, vs2, depth), Lattice[Flat[VarName]].widen(sym1, sym2, depth))
      }
    }

    override def bot: AStore = AbstractStore(Map.empty)

    override def top: AStore = StoreTop

    override def lub(a1: AStore, a2: AStore): AStore = upperBound(a1, a2) { (v1, v2) =>
      (v1, v2) match {
        case ((vs1, sym1), (vs2, sym2)) => (Lattice[ValueShape].lub(vs1, vs2), Lattice[Flat[VarName]].lub(sym1, sym2))
      }
    }

    private def upperBound(a1: AStore, a2: AStore)(vlub: (AValue, AValue) => AValue) = {
      (a1, a2) match {
        case (StoreTop, _) | (_, StoreTop) => StoreTop
        case (AbstractStore(store1), AbstractStore(store2)) =>
          AbstractStore((store1.keySet union store2.keySet).toList.map { vari =>
            val v1 = store1.get(vari).fold((Lattice[ValueShape].bot, Lattice[Flat[VarName]].bot))(identity)
            val v2 = store2.get(vari).fold((Lattice[ValueShape].bot, Lattice[Flat[VarName]].bot))(identity)
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
            val (vs1, sym1) = store1(vari)
            val (vs2, sym2) = store2(vari)
            vari -> (Lattice[ValueShape].glb(vs1, vs2), Lattice[Flat[VarName]].glb(sym1, sym2))
          }.toMap)
      }
    }
  }

  implicit def AMemoriesLattice : Lattice[AMemories] = new Lattice[AMemories] {
    override def bot: AMemories = AMemories(Set())

    override def top: AMemories =
    ???
      //AMemories(Set((SuccessResult((Lattice[ValueShape].top, Lattice[Flat[VarName]].top)), Lattice[AStore].top, Lattice[RelCt].top)))

    override def lub(a1: AMemories, a2: AMemories): AMemories = ???

    override def glb(a1: AMemories, a2: AMemories): AMemories = ???

    override def <=(a1: AMemories, a2: AMemories): Boolean = ???

    override def widen(a1: AMemories, a2: AMemories, depth: Int): AMemories = ???
  }
}
