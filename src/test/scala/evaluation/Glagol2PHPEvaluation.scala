package evaluation

import scalaz.\/-
import semantics.{AbstractRefinementTypeExecutor, ModuleTranslator, TypeWidening}
import semantics.domains.abstracting.{RefinementTypeOps, Refinements, TypeStoreV, VoideableRefinementType}
import syntax.DataType
import util.rascalwrapper.RascalWrapper

class Glagol2PHPEvaluation extends Evaluation("glagol-2-php-evaluation") {

  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The expression translation in Glagol2PHP.rsc" should
      s"only produce simple PHP expressions for simple Glagol expressions using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/Glagol2PHPExpr.rsc").getFile)
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
        val simpleExpr = rtops.excluding("Expression",
          Set("invoke", "invoke2", "new", "get", "fieldAccess", "fieldAccess2", "list", "map", "arrayAccess", "this"))
        val initialStore = TypeStoreV(Map("expr" -> VoideableRefinementType(possiblyVoid = false, simpleExpr)))
        AbstractRefinementTypeExecutor.execute(moddef, "toPhpExpr",
          initialStore = Some(initialStore), initialRefinements = rtops.refinements,
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("PhpExpr"), Some(memoinfo), Some(duration), confname)
      }
    }
  }

  forAll(configs) { (refinement, memowidening) =>
    val confname = Evaluation.refinementWideningName(refinement, memowidening)
    "The expression translation in Glagol2PHP.rsc" should
      s"should not produce unary expressions if there is no unary negation or positive markers using $confname" in {
      val mod = RascalWrapper.loadModuleFromFile(getClass.getResource("/Glagol2PHPExpr.rsc").getFile)
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
        val simpleExpr = rtops.excluding("Expression", Set("negative", "positive"))
        val initialStore = TypeStoreV(Map("expr" -> VoideableRefinementType(possiblyVoid = false, simpleExpr)))
        AbstractRefinementTypeExecutor.execute(moddef, "toPhpExpr",
          initialStore = Some(initialStore), initialRefinements = initialRefinements,
          refinedMatches = refinement, memoWidening = memowidening)
      }
      modExecRes shouldBe a[\/-[_]]
      modExecRes.foreach { case (module, refinements, tmems, memoinfo, duration) =>
        memsOK(module, refinements, tmems, DataType("PhpExpr"), Some(memoinfo), Some(duration), confname)
      }
    }
  }

}
