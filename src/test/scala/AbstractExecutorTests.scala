import com.typesafe.scalalogging.Logger
import org.scalatest.{FlatSpec, Matchers}
import org.slf4j.LoggerFactory
import semantics.domains.abstracting.{Refinements, TypeMemories, TypeMemory, VoideableRefinementType}
import semantics.domains.common.{AssertionError, Break, Continue, Error, EscapedControlOperator, Exceptional, ExceptionalResult, Fail, FieldError, InvalidOperationError, Module, NotEnumerableError, OtherError, ReconstructError, Return, SignatureMismatch, SuccessResult, Throw, TypeError, UnassignedVarError}
import semantics.typing.AbstractTyping
import syntax.Type

/**
  * Created by asal on 26/10/2017.
  */
abstract class AbstractExecutorTests(loggername: String) extends FlatSpec with Matchers {
  val logger = Logger(LoggerFactory.getLogger(loggername))

  protected
  def memsOK(module: Module, refinements: Refinements, mems: TypeMemories[VoideableRefinementType, Unit], targetType: Type): Unit = {
    logger.info("=" * 100)
    refinements.prettyDefs.sorted.foreach(x => logger.info(x))
    logger.info(TypeMemories.pretty(mems))
    logger.info("=" * 100)
    val atyping = AbstractTyping(module)
    mems.memories.exists { case TypeMemory(res, _) =>
      res match {
        case SuccessResult(_) => true
        case _ => false
      }
    } shouldBe true
    mems.memories.foreach { case TypeMemory(res, _) => res match {
      case SuccessResult(restype) =>
        atyping.inferType(restype.refinementType) shouldBe targetType
      case ExceptionalResult(exres) =>
    }
    }
  }
}
