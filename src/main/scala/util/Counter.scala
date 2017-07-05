package util

class Counter(value : BigInt) extends Ref[BigInt](value) {
  def +=(diff : BigInt): BigInt = {
    val oldValue = !this
    this := oldValue + diff
    oldValue
  }

  def -=(diff : BigInt): BigInt = {
    this += -diff
  }

  def ++ : BigInt = {
    this += 1
  }

  def -- : BigInt = {
    this -= 1
  }
}

object Counter {
  def apply(value : BigInt) = new Counter(value)
}
