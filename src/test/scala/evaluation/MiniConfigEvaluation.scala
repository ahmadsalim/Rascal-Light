package evaluation

import scalaz.\/-
import semantics.{AbstractRefinementTypeExecutor, ModuleTranslator}
import semantics.domains.abstracting.{RefinementTypeOps, Refinements, TypeStoreV, VoideableRefinementType}
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class MiniConfigEvaluation extends Evaluation("mini-config-evaluation") {

  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The modernization transformation with only ifelse in MiniConfigMod.rsc" should
      s"run correctly producing no postcondExc with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/MiniConfigMod.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        val transmodule = ModuleTranslator.translateModule(moddef)
        transmodule shouldBe a[\/-[_]]
        val datatypes = transmodule.fold({ _ => throw new Exception("-\\/") },
          mtr => {
            mtr.semmod.datatypes.transform((_, conss) =>
              mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
          })
        val initialRefinements = new Refinements(Map())
        val rtops = RefinementTypeOps(datatypes, initialRefinements)
        val simpleStmt = rtops.excluding("Statement",
          Set("block", "expr", "if", "switch", "while", "doWhile", "for", "continue", "break", "return"))
        val initialStore = TypeStoreV(Map("stmt" -> VoideableRefinementType(possiblyVoid = false, simpleStmt)))
        AbstractRefinementTypeExecutor.execute(moddef, "modernize",
          refinedMatches = refinement, memoWidening = memowidening,
          initialStore = Some(initialStore), initialRefinements = initialRefinements)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Expression"), Some(memoinfo), Some(duration), confname)
      }
    }
  }

  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The modernization transformation with only relevant expressions in MiniConfigMod.rsc" should
      s"run correctly producing only relevant and ternary expressions with the abstract type executor using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/MiniConfigMod.rsc").getFile)
      val modExecRes = mod.flatMap { moddef =>
        val transmodule = ModuleTranslator.translateModule(moddef)
        transmodule shouldBe a[\/-[_]]
        val datatypes = transmodule.fold({ _ => throw new Exception("-\\/") },
          mtr => {
            mtr.semmod.datatypes.transform((_, conss) =>
              mtr.semmod.constructors.filterKeys(conss.contains).mapValues(_._2.map(_.typ)))
          })
        val initialRefinements = new Refinements(Map())
        val rtops = RefinementTypeOps(datatypes, initialRefinements)
        val simpleStmt = rtops.excluding("Statement",
          Set("block", "expr", "if", "switch", "while", "doWhile", "for", "continue", "break", "return"))
        val simpleExpr = rtops.excluding("Expression", Set("call", "sizeof", "assign", "ternary", "postop"))
        val refineStmt = rtops.refineSub(simpleStmt, "Expression", simpleExpr)
        val initialStore = TypeStoreV(Map("stmt" -> VoideableRefinementType(possiblyVoid = false, refineStmt)))
        AbstractRefinementTypeExecutor.execute(moddef, "modernize",
          refinedMatches = refinement, memoWidening = memowidening,
          initialStore = Some(initialStore), initialRefinements = rtops.refinements)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("Expression"), Some(memoinfo), Some(duration), confname)
      }
    }
  }

}
