package semantics.domains

import scala.language.higherKinds

package object common {
  type Sum1[E,F1[_]] = Sum2[E, F1, Nothing]
  type Sum2[E,F1[_],F2[_]] = Sum3[E, F1, F2, Nothing]
  type Sum3[E,F1[_],F2[_],F3[_]] = Sum4[E, F1, F2, F3, Nothing]
  type Sum4[E,F1[_],F2[_],F3[_],F4[_]] = Sum5[E, F1, F2, F3, F4, Nothing]
}
