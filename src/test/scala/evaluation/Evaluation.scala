package evaluation

import helper.AbstractExecutorTests
import org.scalatest.prop._
import org.scalatest.concurrent._
import org.scalatest.time.Span
import org.scalatest.time.SpanSugar._
import scalaz.\/-
import semantics.domains.abstracting._
import semantics.{AbstractRefinementTypeExecutor, ConstructorWidening, ModuleTranslator, SimpleWidening, TypeWidening}
import syntax.{DataType, ListType}
import util.rascalwrapper.RascalWrapper

abstract class Evaluation(loggername: String) extends AbstractExecutorTests(loggername) with PropertyChecks with TimeLimitedTests {
  val configs = Table(
    ("refinement", "widening"),
    //(false, SimpleWidening),
    (false, TypeWidening),
    (false, ConstructorWidening(1)),
    //(true, SimpleWidening),
    (true, TypeWidening),
    (true, ConstructorWidening(1))
  )

  override def timeLimit: Span = 100.seconds

  override val defaultTestSignaler: Signaler = (testThread: Thread) => testThread.interrupt()
}
