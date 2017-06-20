package semantics

import semantics.domains.common.{Domains, ExprFunBody, Module}
import syntax._

import scalaz.\/
import scalaz.std.list._
import scalaz.syntax.either._
import scalaz.syntax.foldable._

case class ModuleTranslationResult(globalVarDefs: List[(VarName, Expr)], tests: List[TestDef], semmod: Module)

object ModuleTranslator {

  private
  def alreadyDefined(name: Name, outmod: Module): Boolean = {
    outmod.funs.contains(name) || outmod.globalVars.contains(name) ||
      outmod.datatypes.contains(name) || outmod.constructors.contains(name)
  }

  private
  def alreadyDefinedErrMsg(name: Name) = s"duplicate definition in module of name: $name"

  private
  def constructorTypeSameNameErrMsg(name: Name) = s"constructor $name has the same name as the data type"

  /**
    * Translate a syntactic Rascal Light module to a semantic one
    * @param module Definitionf syntactic Rascal Light module
    * @return List of unevaluated global variables, tests and the semantic equivalent module if successful,
    *         and otherwise a string describing an error during translation
    */
  def translateModule(module: ModuleDef): String \/ ModuleTranslationResult = {
    module.defs.toList.foldLeftM[String \/ ?, ModuleTranslationResult](
      ModuleTranslationResult(List.empty, List.empty, Domains.prelude)) { (st, df) =>
      val ModuleTranslationResult(unevalglobvars, tests, outmod) = st
      df match {
        case GlobalVarDef(typ, name, initialValue) =>
          if (alreadyDefined(name, outmod)) alreadyDefinedErrMsg(name).left
          else ModuleTranslationResult((name, initialValue) :: unevalglobvars, tests,
            outmod.copy(globalVars = outmod.globalVars.updated(name, typ))).right
        case FunDef(returntype, name, parameters, body) =>
          if (alreadyDefined(name, outmod)) alreadyDefinedErrMsg(name).left
          else ModuleTranslationResult(unevalglobvars, tests,
            outmod.copy(funs = outmod.funs.updated(name, (returntype, parameters.toList, ExprFunBody(body))))).right
        case DataDef(tyname, constructors) =>
          if (alreadyDefined(tyname, outmod)) alreadyDefinedErrMsg(tyname).left
          else {
            val consmapr = constructors.toList.foldLeftM[String \/ ?, Map[ConsName, (TypeName, List[Parameter])]](
              Map.empty
            ) { (consmap, cdf) =>
              if (alreadyDefined(cdf.name, outmod)) alreadyDefinedErrMsg(cdf.name).left
              else if (cdf.name == tyname) constructorTypeSameNameErrMsg(cdf.name).left
              else consmap.updated(cdf.name, (tyname, cdf.parameters.toList)).right
            }
            consmapr.map { consmap =>
              ModuleTranslationResult(unevalglobvars, tests,
                outmod.copy(datatypes = outmod.datatypes.updated(tyname, constructors.map(_.name).toList),
                  constructors = outmod.constructors ++ consmap))
            }
          }
        case td: TestDef => ModuleTranslationResult(unevalglobvars, tests :+ td, outmod).right
      }
    }
  }
}
