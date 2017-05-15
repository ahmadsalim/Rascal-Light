package semantics.domains.common

/**
  * Created by asal on 15/05/2017.
  */
trait ConcreteAbstractGalois[DC, DA] {
  def alpha(dcs : Set[DC]): DA
  def gamma(da: DA, bound: Int): Set[DC]
}

object Galois {
  implicit class ConcreteAbstractGaloisAbstractOps[DC, DA](da : DA)(implicit cagalois : ConcreteAbstractGalois[DC, DA]) {
    final def gamma(bound: Int = 3): Set[DC] = cagalois.gamma(da, bound)

    // Unicode
    final def γ(bound: Int = 3): Set[DC] = gamma(bound)
  }

  implicit class ConcreteAbstractGaloisConcreteOps[DC, DA](dcs : Set[DC])(implicit cagalois : ConcreteAbstractGalois[DC, DA]) {
    final def alpha : DA = cagalois.alpha(dcs)

    // Unicode
    final def ɑ : DA = alpha
  }
}
