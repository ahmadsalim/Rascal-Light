import org.scalatest.concurrent._
import org.scalatest.time.Span
import semantics.{AbstractRefinementTypeExecutor, ModuleTranslator}
import semantics.domains.abstracting._
import syntax.{DataType, ListType}
import util.rascalwrapper.RascalWrapper

import scalaz.\/-
import org.scalatest.time.SpanSugar._

class Evaluation extends AbstractExecutorTests("evaluation") with TimeLimitedTests {

  "The negation normal form transformation in NNF.rsc" should "run correctly with the abstract type executor" in {
    val modNnfO = RascalWrapper.loadModuleFromFile(getClass.getResource("NNF.rsc").getFile)
    val modNnfExecRes = modNnfO.flatMap { moddef =>
      val transmodule = ModuleTranslator.translateModule(moddef)
      transmodule shouldBe a [\/-[_]]
      val datatypes = transmodule.fold({_ =>  throw new Exception("-\\/") },
        mtr => {
          mtr.semmod.datatypes.transform((_, conss) =>
            mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
        })
      val initialRefinements = new Refinements(Map())
      val rtops = RefinementTypeOps(datatypes, initialRefinements)
      val ordinaryFormula = rtops.excluding("Formula", Set("begin"))
      val initialStore = TypeStoreV(Map("phi" -> VoideableRefinementType(possiblyVoid = false, ordinaryFormula)))
      AbstractRefinementTypeExecutor.execute(moddef, "nnf", initialStore = Some(initialStore), initialRefinements = initialRefinements)
    }
    modNnfExecRes shouldBe a [\/-[_]]
    modNnfExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("Formula"))
    }
  }

  "The rename field refactoring in RenameStructField.rsc" should "run correctly with the abstract type executor" in {
    val modRFO = RascalWrapper.loadModuleFromFile(getClass.getResource("RenameStructField.rsc").getFile)
    val modRFExecRes = modRFO.flatMap { moddef =>
      val ofnrn = new Refinement("Nominal#ofn")
      val nfnrn = new Refinement("Nominal#nfn")
      val initialRefinements: Refinements =
        new Refinements(Map(ofnrn -> RefinementDef("Nominal#ofn", Map("ofn" -> List())),
          nfnrn -> RefinementDef("Nominal#nfn", Map("nfn" -> List()))))
      val initialStore =
        TypeStoreV(Map(
          "pkg" -> VoideableRefinementType(possiblyVoid = false, DataRefinementType("Package", None)),
          "st" -> VoideableRefinementType(possiblyVoid = false, BaseRefinementType(StringRefinementType)),
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

  "The desugaring in DesugarOberonSimpl.rsc" should "run correctly with the abstract type executor" in {
    val modDSOb = RascalWrapper.loadModuleFromFile(getClass.getResource("DesugarOberonSimpl.rsc").getFile)
    val modDSObExecRes = modDSOb.flatMap { moddef =>
      AbstractRefinementTypeExecutor.execute(moddef, "desugar")
    }
    modDSObExecRes shouldBe a [\/-[_]]
    modDSObExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("Module"))
    }
  }

  "The expression translation in Glagol2PHP.rsc" should "only produce simple PHP expressions for simple Glagol expressions" in {
    val modG2P = RascalWrapper.loadModuleFromFile(getClass.getResource("Glagol2PHPExpr.rsc").getFile)
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

  "The expression translation in Glagol2PHP.rsc" should "should not produce unary expressions if there is no unary negation or positive markers" in {
    val modG2P = RascalWrapper.loadModuleFromFile(getClass.getResource("Glagol2PHPExpr.rsc").getFile)
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

  "The simplification procedure in MiniCalc.rsc" should "run correctly with the abstract type executor" in {
    val modMC = RascalWrapper.loadModuleFromFile(getClass.getResource("MiniCalc.rsc").getFile)
    val modMCExecRes = modMC.flatMap { moddef =>
      AbstractRefinementTypeExecutor.execute(moddef, "simplify")
    }
    modMCExecRes shouldBe a [\/-[_]]
    modMCExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("CExpr"))
    }
  }

  "The type inference procedure in MiniCalc.rsc" should "run correctly with the abstract type executor" in {
    val modMC = RascalWrapper.loadModuleFromFile(getClass.getResource("MiniCalc.rsc").getFile)
    val modMCExecRes = modMC.flatMap { moddef =>
      val transmodule = ModuleTranslator.translateModule(moddef)
      transmodule shouldBe a[\/-[_]]
      val datatypes = transmodule.fold({ _ => throw new Exception("-\\/") },
        mtr => {
          mtr.semmod.datatypes.transform((_, conss) =>
            mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
        })
      val initialRefinements: Refinements = new Refinements
      val rtops = RefinementTypeOps(datatypes, initialRefinements)
      val onlyIntExprs = rtops.excluding("CExpr", Set("cstb", "let", "var", "leq", "and", "not", "ifte"))
      val initialStore: TypeStore =
        TypeStoreV(Map(
          "e" -> VoideableRefinementType(possiblyVoid = false, onlyIntExprs)
        ))
      AbstractRefinementTypeExecutor.execute(moddef, "inferTypeC", initialRefinements = initialRefinements, initialStore = Some(initialStore))
    }
    modMCExecRes shouldBe a [\/-[_]]
    modMCExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("CType"))
    }
  }

  "The evaluation procedure in MiniCalc.rsc" should "run correctly with the abstract type executor" in {
    val modMC = RascalWrapper.loadModuleFromFile(getClass.getResource("MiniCalc.rsc").getFile)
    val modMCExecRes = modMC.flatMap { moddef =>
      val transmodule = ModuleTranslator.translateModule(moddef)
      transmodule shouldBe a[\/-[_]]
      val datatypes = transmodule.fold({ _ => throw new Exception("-\\/") },
        mtr => {
          mtr.semmod.datatypes.transform((_, conss) =>
            mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
        })
      val initialRefinements: Refinements = new Refinements
      val rtops = RefinementTypeOps(datatypes, initialRefinements)
      val noCstiLets = rtops.excluding("CExpr", Set("csti", "let"))
      val initialStore: TypeStore =
        TypeStoreV(Map(
          "e" -> VoideableRefinementType(possiblyVoid = false, noCstiLets)
        ))
      AbstractRefinementTypeExecutor.execute(moddef, "evalC", initialRefinements = initialRefinements, initialStore = Some(initialStore))
    }
    modMCExecRes shouldBe a [\/-[_]]
    modMCExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("CVal"))
    }
  }

  "The compilation procedure in MiniCalc.rsc" should "run correctly with the abstract type executor" in {
    val modMC = RascalWrapper.loadModuleFromFile(getClass.getResource("MiniCalc.rsc").getFile)
    val modMCExecRes = modMC.flatMap { moddef =>
      val transmodule = ModuleTranslator.translateModule(moddef)
      transmodule shouldBe a[\/-[_]]
      val datatypes = transmodule.fold({ _ => throw new Exception("-\\/") },
        mtr => {
          mtr.semmod.datatypes.transform((_, conss) =>
            mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
        })
      val initialRefinements: Refinements = new Refinements
      val rtops = RefinementTypeOps(datatypes, initialRefinements)
      val noIfCExpr = rtops.excluding("CExpr", Set("ifte"))
      val initialStore: TypeStore =
        TypeStoreV(Map(
          "e" -> VoideableRefinementType(possiblyVoid = false, noIfCExpr),
          "cenv" -> VoideableRefinementType(possiblyVoid = false, ListRefinementType(DataRefinementType("CRVal", None), Intervals.Positive.singleton(0)))
        ))
      AbstractRefinementTypeExecutor.execute(moddef, "compile", initialRefinements = initialRefinements, initialStore = Some(initialStore))
    }
    modMCExecRes shouldBe a[\/-[_]]
    modMCExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, ListType(DataType("CInstr")))
    }
  }

  /*
  TODO Currently running too slowly
  "The modernization transformation in MiniConfigMod.rsc" should "run correctly with the abstract type executor" in {
    val modMCM = RascalWrapper.loadModuleFromFile(getClass.getResource("MiniConfigMod.rsc").getFile)
    val modMCMExecRes = modMCM.flatMap { moddef =>
      AbstractRefinementTypeExecutor.execute(moddef, "modernize")
    }
    modMCMExecRes shouldBe a [\/-[_]]
    modMCMExecRes.foreach { case (module, refinements, tmems) =>
      memsOK(module, refinements, tmems, DataType("Expression"))
    }
  } */

  override def timeLimit: Span = 100.seconds

  override val defaultTestSignaler: Signaler = (testThread: Thread) => testThread.stop
}
