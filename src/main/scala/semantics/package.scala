import scalaz.Monad

/**
  * Created by asal on 23/02/2017.
  */
package object semantics {
  implicit val monadResult = new Monad[Result] {
    override def point[A](a: => A): Result[A] = SuccessResult(a)

    override def bind[A, B](fa: Result[A])(f: (A) => Result[B]): Result[B] = fa match {
      case ExceptionalResult(exres) => ExceptionalResult(exres)
      case SuccessResult(t) => f(t)
    }
  }
}
