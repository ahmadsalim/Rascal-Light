package util

import com.twitter.util.LruMap

import scala.collection.JavaConverters.mapAsScalaMapConverter

private[util]
abstract class Cached[I, O](max: Int) {
  val underlyingCache = LruMap.makeUnderlying[I, O](max).asScala
}

private[util]
class Memoization1[I, O](max: Int)(f: I => O) extends Cached[I, O](max) with ((I) => O) {
  override def apply(i: I): O = underlyingCache.getOrElseUpdate(i, f(i))
}

private[util]
class Memoization2[I1, I2, O](max: Int)(f: (I1, I2) => O) extends Cached[(I1, I2), O](max) with ((I1, I2) => O) {
  override def apply(i1: I1, i2: I2) = underlyingCache.getOrElseUpdate((i1, i2), f(i1, i2))
}

private[util]
class Memoization3[I1, I2, I3, O](max: Int)(f: (I1, I2, I3) => O) extends Cached[(I1, I2, I3), O](max) with ((I1, I2, I3) => O) {
  override def apply(i1: I1, i2: I2, i3: I3) = underlyingCache.getOrElseUpdate((i1, i2, i3), f(i1, i2, i3))
}

private[util]
class Memoization4[I1, I2, I3, I4, O](max: Int)(f: (I1, I2, I3, I4) => O) extends Cached[(I1, I2, I3, I4), O](max) with ((I1, I2, I3, I4) => O) {
  override def apply(i1: I1, i2: I2, i3: I3, i4: I4) = underlyingCache.getOrElseUpdate((i1, i2, i3, i4), f(i1, i2, i3, i4))
}

private[util]
class Memoization5[I1, I2, I3, I4, I5, O](max: Int)(f: (I1, I2, I3, I4, I5) => O) extends Cached[(I1, I2, I3, I4, I5), O](max) with ((I1, I2, I3, I4, I5) => O) {
  override def apply(i1: I1, i2: I2, i3: I3, i4: I4, i5: I5) = underlyingCache.getOrElseUpdate((i1, i2, i3, i4, i5), f(i1, i2, i3, i4, i5))
}

private[util]
class Memoization6[I1, I2, I3, I4, I5, I6, O](max: Int)(f: (I1, I2, I3, I4, I5, I6) => O) extends Cached[(I1, I2, I3, I4, I5, I6), O](max) with ((I1, I2, I3, I4, I5, I6) => O) {
  override def apply(i1: I1, i2: I2, i3: I3, i4: I4, i5: I5, i6: I6) = underlyingCache.getOrElseUpdate((i1, i2, i3, i4, i5, i6), f(i1, i2, i3, i4, i5, i6))
}

object Memoization {
  def memoized[I, O](max: Int)(f: I => O): I => O = new Memoization1[I, O](max)(f)
  def memoized[I1, I2, O](max: Int)(f: (I1, I2) => O): (I1, I2) => O = new Memoization2[I1, I2, O](max)(f)
  def memoized[I1, I2, I3, O](max: Int)(f: (I1, I2, I3) => O): (I1, I2, I3) => O = new Memoization3[I1, I2, I3, O](max)(f)
  def memoized[I1, I2, I3, I4, O](max: Int)(f: (I1, I2, I3, I4) => O): (I1, I2, I3, I4) => O = new Memoization4[I1, I2, I3, I4, O](max)(f)
  def memoized[I1, I2, I3, I4, I5, O](max: Int)(f: (I1, I2, I3, I4, I5) => O): (I1, I2, I3, I4, I5) => O = new Memoization5[I1, I2, I3, I4, I5, O](max)(f)
  def memoized[I1, I2, I3, I4, I5, I6, O](max: Int)(f: (I1, I2, I3, I4, I5, I6) => O): (I1, I2, I3, I4, I5, I6) => O = new Memoization6[I1, I2, I3, I4, I5, I6, O](max)(f)
}
