import semantics.domains.common.{ExceptionalResult, ResultV, SuccessResult}
import semantics.domains.concrete.Value

import scalaz.Monad

/**
  * Created by asal on 23/02/2017.
  */
package object semantics {
  type Result[T] = ResultV[Value, T, Unit]

  implicit def monadResult[V,F] = new Monad[ResultV[V, ?,F]] {
    override def point[A](a: => A): ResultV[V, A, F] = SuccessResult(a)

    override def bind[A, B](fa: ResultV[V, A, F])(f: (A) => ResultV[V, B, F]): ResultV[V, B, F] = fa match {
      case ExceptionalResult(exres) => ExceptionalResult(exres)
      case SuccessResult(t) => f(t)
    }
  }
}
