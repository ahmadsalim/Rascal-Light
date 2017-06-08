package semantics.domains.concrete

import semantics.domains.common.Lattice
import syntax.{ListType, MapType, SetType, Type, ValueType, VoidType}

object TypeOps {
  implicit def TypeLattice = new Lattice[Type] {
    override def bot: Type = VoidType

    override def top: Type = ValueType

    override def lub(t1: Type, t2: Type): Type =
      if (<=(t1, t2)) t2
      else if (<=(t2, t1)) t1
      else ValueType

    override def glb(t1: Type, t2: Type): Type =
      if (<=(t1, t2)) t1
      else if (<=(t2, t1)) t2
      else VoidType

    override def <=(t1: Type, t2: Type): Boolean = (t1, t2) match {
        case _ if t1 == t2 => true
        case (VoidType, _) => true
        case (_, ValueType) => true
        case (ListType(t1_), ListType(t2_)) => <=(t1_, t2_)
        case (SetType(t1_), SetType(t2_)) => <=(t1_, t2_)
        case (MapType(tk1, tv1), MapType(tk2, tv2)) => <=(tk1, tk2) && <=(tv1, tv2)
        case _ => false
      }

    override def widen(a1: Type, a2: Type, depth: Int): Type = lub(a1, a2)
  }

}
