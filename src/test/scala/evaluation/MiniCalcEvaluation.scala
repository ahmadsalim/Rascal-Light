package evaluation

import scalaz.\/-
import semantics.{AbstractRefinementTypeExecutor, ModuleTranslator}
import semantics.domains.abstracting._
import syntax.{DataType, ListType}
import util.rascalwrapper.RascalWrapper
import org.scalatest.prop.TableDrivenPropertyChecks._

class MiniCalcEvaluation extends Evaluation("mini-calc-evaluation") {
  forAll(configs) { (refinement, memowidening) =>
    "The simplification procedure in MiniCalc.rsc" should
      s"run correctly with the abstract type executor using ${Evaluation.refinementWideningName(refinement, memowidening)}" in {
      val modMC = RascalWrapper.loadModuleFromFile(getClass.getResource("/MiniCalc.rsc").getFile)
      val modMCExecRes = modMC.flatMap { moddef =>
        AbstractRefinementTypeExecutor.execute(moddef, "simplify",
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modMCExecRes shouldBe a[\/-[_]]
      modMCExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("CExpr"), Some(memoinfo), Some(duration))
      }
    }
  }

  forAll(configs) { (refinement, memowidening) =>
    "The type inference procedure in MiniCalc.rsc" should
      s"run correctly with the abstract type executor using ${Evaluation.refinementWideningName(refinement, memowidening)}" in {
      val modMC = RascalWrapper.loadModuleFromFile(getClass.getResource("/MiniCalc.rsc").getFile)
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
        AbstractRefinementTypeExecutor.execute(moddef, "inferTypeC",
          initialRefinements = initialRefinements, initialStore = Some(initialStore),
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modMCExecRes shouldBe a[\/-[_]]
      modMCExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("CType"), Some(memoinfo), Some(duration))
      }
    }
  }

  forAll(configs) { (refinement, memowidening) =>
    "The evaluation procedure in MiniCalc.rsc" should
      s"run correctly with the abstract type executor using ${Evaluation.refinementWideningName(refinement, memowidening)}" in {
      val modMC = RascalWrapper.loadModuleFromFile(getClass.getResource("/MiniCalc.rsc").getFile)
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
        AbstractRefinementTypeExecutor.execute(moddef, "evalC",
          initialRefinements = initialRefinements, initialStore = Some(initialStore),
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modMCExecRes shouldBe a[\/-[_]]
      modMCExecRes.foreach { case (module, refinements, tmems, meminfo, duration) =>
        memsOK(module, refinements, tmems, DataType("CVal"), Some(meminfo), Some(duration))
      }
    }
  }

  forAll(configs) { (refinement, memowidening) =>
    "The compilation procedure in MiniCalc.rsc" should
      s"run correctly with the abstract type executor using ${Evaluation.refinementWideningName(refinement, memowidening)}" in {
      val modMC = RascalWrapper.loadModuleFromFile(getClass.getResource("/MiniCalc.rsc").getFile)
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
        AbstractRefinementTypeExecutor.execute(moddef, "compile",
          initialRefinements = initialRefinements, initialStore = Some(initialStore),
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modMCExecRes shouldBe a[\/-[_]]
      modMCExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, ListType(DataType("CInstr")), Some(memoinfo), Some(duration))
      }
    }
  }
}
