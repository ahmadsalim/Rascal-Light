import semantics.domains.common.{ExceptionalResult, ResultV, SuccessResult}
import semantics.domains.concrete.Value

import scalaz.Monad

/**
  * Created by asal on 23/02/2017.
  */
package object semantics {
  type Result[T] = ResultV[Value, T]

  implicit def monadResult[V] = new Monad[ResultV[V, ?]] {
    override def point[A](a: => A): ResultV[V, A] = SuccessResult(a)

    override def bind[A, B](fa: ResultV[V, A])(f: (A) => ResultV[V, B]): ResultV[V, B] = fa match {
      case ExceptionalResult(exres) => ExceptionalResult(exres)
      case SuccessResult(t) => f(t)
    }
  }
}
