package semantics.domains

import scala.language.higherKinds

package object common {
  type Sum0[E] = Sum5[E, Nothing, Nothing, Nothing, Nothing, Nothing]
  type Sum1[E,F1[_]] = Sum5[E, F1, Nothing, Nothing, Nothing, Nothing]
  type Sum2[E,F1[_],F2[_]] = Sum5[E, F1, F2, Nothing, Nothing, Nothing]
  type Sum3[E,F1[_],F2[_],F3[_]] = Sum5[E, F1, F2, F3, Nothing, Nothing]
  type Sum4[E,F1[_],F2[_],F3[_],F4[_]] = Sum5[E, F1, F2, F3, F4, Nothing]
}
