import org.scalatest.{FlatSpec, Matchers}
import semantics.{AbstractRefinementTypeExecutor, ModuleTranslator}
import semantics.domains.abstracting._
import semantics.domains.common._
import semantics.typing.AbstractTyping
import syntax.{DataType, StringType, Type}
import util.rascalwrapper.RascalWrapper

import scalaz.{\/, \/-}

/**
  * Created by asal on 20/06/2017.
  */
class AbstractRefinementTypeExecutorTests extends FlatSpec with Matchers {
  private def checkError(exres: Exceptional[VoideableRefinementType]) = {
    //exres shouldNot be(an[Error])
  }

  private
  def memsOK(module: Module, refinements: Refinements, mems: TypeMemories[VoideableRefinementType], targetType: Type): Unit = {
    println("=" * 100)
    refinements.prettyDefs.sorted.foreach(println)
    println(TypeMemories.pretty(mems))
    println("=" * 100)
    val atyping = AbstractTyping(module)
    mems.memories.exists { case TypeMemory(res, _) =>
      res match {
        case SuccessResult(_) => true
        case _ => false
      }
    } shouldBe true
    mems.memories.foreach { case TypeMemory(res, _) => res match {
        case SuccessResult(restype) =>
          //restype.possiblyVoid shouldBe false
          atyping.inferType(restype.refinementType) shouldBe targetType
        case ExceptionalResult(exres) =>  checkError(exres)
      }
    }
  }

  /*
  "The expression simplification procedure in Expr.rscli" should "run correctly with the abstract type executor" in {
    val modExprO = RascalWrapper.loadModuleFromFile(getClass.getResource("Expr.rscli").getFile)
    val modExprExecRes = modExprO.flatMap { moddef =>
      AbstractRefinementTypeExecutor.execute(moddef, "simplify")
    }
    modExprExecRes shouldBe a [\/-[_]]
    modExprExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("Expr"))
    }
  }

    "The extract superclass refactoring in ExtractSuperclass.rscli" should "run correctly with the abstract type executor" in {
      val modESO = RascalWrapper.loadModuleFromFile(getClass.getResource("ExtractSuperclass.rscli").getFile)
      val modESExecRes = modESO.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "extractSuperclass")
      }
      modESExecRes shouldBe a [\/-[_]]
      modESExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Package"))
      }
    }

    "The replace delegation with inheritance refactoring in ReplaceDelegation.rscli" should "run correctly with the abstract type executor" in {
      val modRDO = RascalWrapper.loadModuleFromFile(getClass.getResource("ReplaceDelegation.rscli").getFile)
      val modRDExecRes = modRDO.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "replaceDelegationWithInheritance")
      }
      modRDExecRes shouldBe a [\/-[_]]
      modRDExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Package"))
      }
    }

    "The simplification procedure in SimplifyTableau.rscli" should "run correctly with the abstract type executor" in {
      val modSTab = RascalWrapper.loadModuleFromFile(getClass.getResource("SimplifyTableau.rscli").getFile)
      val modSTabExecRes = modSTab.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "simplify")
      }
      modSTabExecRes shouldBe a [\/-[_]]
      modSTabExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Tableau"))
      }
    }*/

  "The negation normal form transformation in NNF.rscli" should "run correctly with the abstract type executor" in {
    val modNnfO = RascalWrapper.loadModuleFromFile(getClass.getResource("NNF.rscli").getFile)
    val modNnfExecRes = modNnfO.flatMap { moddef =>
      AbstractRefinementTypeExecutor.execute(moddef, "nnf")
    }
    modNnfExecRes shouldBe a [\/-[_]]
    modNnfExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("Formula"))
    }
  }


  "The rename field refactoring in RenameStructField.rscli" should "run correctly with the abstract type executor" in {
    val modRFO = RascalWrapper.loadModuleFromFile(getClass.getResource("RenameStructField.rscli").getFile)
    val modRFExecRes = modRFO.flatMap { moddef =>
      val ofnrn = new Refinement("Nominal#ofn")
      val nfnrn = new Refinement("Nominal#nfn")
      val initialRefinements: Refinements =
        new Refinements(Map(ofnrn -> RefinementDef("Nominal#ofn", Map("ofn" -> List())),
          nfnrn -> RefinementDef("Nominal#nfn", Map("nfn" -> List()))))
      val initialStore =
        TypeStoreV(Map(
          "pkg" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Package", None)),
          "st" -> VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringType)),
          "oldFieldName" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Nominal", Some(ofnrn))),
          "newFieldName" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Nominal", Some(nfnrn)))
        ))
      AbstractRefinementTypeExecutor.execute(moddef, "renameField", initialStore = Some(initialStore), initialRefinements = initialRefinements)
    }
    modRFExecRes shouldBe a [\/-[_]]
    modRFExecRes.foreach {  case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("Package"))
    }
  }


    "The desugaring in DesugarOberonSimpl.rscli" should "run correctly with the abstract type executor" in {
      val modDSOb = RascalWrapper.loadModuleFromFile(getClass.getResource("DesugarOberonSimpl.rscli").getFile)
      val modDSObExecRes = modDSOb.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "desugar")
      }
      modDSObExecRes shouldBe a [\/-[_]]
      modDSObExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("Module"))
      }
    }
    "The expression translation in Glagol2PHP.rscli" should "only produce simple PHP expressions for simple Glagol expressions" in {
      val modG2P = RascalWrapper.loadModuleFromFile(getClass.getResource("Glagol2PHPExpr.rscli").getFile)
      val modG2PExecRes = modG2P.flatMap { moddef =>
        val transmodule = ModuleTranslator.translateModule(moddef)
        transmodule shouldBe a [\/-[_]]
        val datatypes = transmodule.fold({_ =>  throw new Exception("-\\/") },
          mtr => {
           mtr.semmod.datatypes.transform((_, conss) =>
             mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
          })
        val initialRefinements = new Refinements(Map())
        val rtops = RefinementTypeOps(datatypes, initialRefinements)
        val simpleExpr = rtops.excluding("Expression",
          Set("invoke", "invoke2", "new", "get", "fieldAccess", "fieldAccess2", "list", "map", "arrayAccess", "this"))
        val initialStore = TypeStoreV(Map("expr" -> VoideableRefinementType(possiblyVoid = false, simpleExpr)))
        AbstractRefinementTypeExecutor.execute(moddef, "toPhpExpr", precise = false,
          initialStore = Some(initialStore), initialRefinements = initialRefinements)
      }
      modG2PExecRes shouldBe a [\/-[_]]
      modG2PExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("PhpExpr"))
      }
    }

    "The expression translation in Glagol2PHP.rscli" should "should not produce unary expressions if there is no unary negation or positive markers" in {
      val modG2P = RascalWrapper.loadModuleFromFile(getClass.getResource("Glagol2PHPExpr.rscli").getFile)
      val modG2PExecRes = modG2P.flatMap { moddef =>
        val transmodule = ModuleTranslator.translateModule(moddef)
        transmodule shouldBe a [\/-[_]]
        val datatypes = transmodule.fold({_ =>  throw new Exception("-\\/") },
          mtr => {
            mtr.semmod.datatypes.transform((_, conss) =>
              mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
          })
        val initialRefinements = new Refinements(Map())
        val rtops = RefinementTypeOps(datatypes, initialRefinements)
        val simpleExpr = rtops.excluding("Expression",
          Set("negative", "positive"))
        val initialStore = TypeStoreV(Map("expr" -> VoideableRefinementType(possiblyVoid = false, simpleExpr)))
        AbstractRefinementTypeExecutor.execute(moddef, "toPhpExpr", precise = false,
          initialStore = Some(initialStore), initialRefinements = initialRefinements)
      }
      modG2PExecRes shouldBe a [\/-[_]]
      modG2PExecRes.foreach { case (module, refinements, tmems) =>
        memsOK(module, refinements, tmems, DataType("PhpExpr"))
      }
    }
}