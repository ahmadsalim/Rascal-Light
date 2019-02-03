package helper

import java.time.Duration

import com.typesafe.scalalogging.Logger
import org.scalatest.{FlatSpec, Matchers}
import org.slf4j.LoggerFactory
import scalaz.Optional
import semantics.domains.abstracting.{Refinements, TypeMemories, TypeMemory, VoideableRefinementType}
import semantics.domains.common.{ExceptionalResult, Module, SuccessResult}
import semantics.typing.AbstractTyping
import syntax.Type

/**
  * Created by asal on 26/10/2017.
  */
abstract class AbstractExecutorTests(loggername: String) extends FlatSpec with Matchers {
  val logger = Logger(LoggerFactory.getLogger(loggername))

  protected
  def memsOK(module: Module, refinements: Refinements,
             mems: TypeMemories[VoideableRefinementType, Unit], targetType: Type,
             memoInfo: Option[(Int, Int, Int)] = None,
             duration: Option[Duration] = None): Unit = {
    logger.info("=" * 100)
    refinements.prettyDefs.sorted.foreach(x => logger.info(x))
    logger.info(TypeMemories.pretty(mems))
    logger.info("\n")
    memoInfo.foreach { case (misses, hits, widenings) =>
      logger.info(s"memo misses: $misses, hits: $hits, widenings: $widenings");
    }
    duration.foreach { duration =>
      logger.info(s"duration: ${duration.toMinutesPart}:${duration.toSecondsPart}:${duration.toMillisPart}")
    }
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
