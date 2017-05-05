import org.scalatest.{FlatSpec, Matchers}
import util.rascalwrapper.RascalWrapper

import scala.io.Source
import scalaz.\/-

/**
  * Created by asal on 05/05/2017.
  */
class RascalWrapperParsingTests extends FlatSpec with Matchers {
  "The wrapped parser" should "parse Expr.rscli correctly" in {
    val resource = getClass.getResource("Expr.rscli")
    val parsed = RascalWrapper.parseRascal(resource.getFile)
    val translated = RascalWrapper.translateModule(parsed)
    translated shouldBe a [\/-[_]]
  }
}
