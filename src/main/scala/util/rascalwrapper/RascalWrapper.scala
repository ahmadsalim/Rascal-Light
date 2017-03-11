package util.rascalwrapper

import scala.collection.JavaConverters._
import java.io.File
import java.nio.file.Files

import org.rascalmpl.ast.Declaration.{Data, Function, Variable}
import org.rascalmpl.ast.Name.Lexical
import org.rascalmpl.ast.{Declaration, Expression, Module, Type}
import org.rascalmpl.library.lang.rascal.syntax.RascalParser
import org.rascalmpl.parser.{ASTBuilder, Parser}
import org.rascalmpl.parser.gtd.result.out.DefaultNodeFlattener
import org.rascalmpl.parser.uptr.UPTRNodeFactory
import syntax.GlobalVarDef

import scalaz.\/
import scalaz.syntax.either._
import scalaz.std.either._
import scalaz.std.list._
import scalaz.syntax.traverse._
import scalaz.syntax.monad._

object RascalWrapper {
  def parseRascal(path: String): Module = {
    val parser = new RascalParser()
    val file = new File(path)
    val input = new String(Files.readAllBytes(file.toPath))
    val astbuilder = new ASTBuilder()
    val parsed = parser.parse(Parser.START_MODULE, file.toURI, input.toCharArray, new DefaultNodeFlattener(), new UPTRNodeFactory())
    astbuilder.buildModule(parsed)
  }

  def translateFunction(function: Function): String \/ List[syntax.FunDef] = ???

  def translateData(data: Data): String \/ List[syntax.DataDef] = ???

  def translateType(getType: Type): String \/ syntax.Type = ???

  def translateExpr(getInitial: Expression): String \/ syntax.Expr = ???

  def translateGlobalVariable(variable: Variable): String \/ List[syntax.GlobalVarDef] = {
    val vartyr = translateType(variable.getType)
    val vars = variable.getVariables.asScala.toList
    vartyr.flatMap(varty =>
      vars.map(vr =>
        if (vr.hasInitial) {
          val exprr = translateExpr(vr.getInitial)
          exprr.map(expr => GlobalVarDef(varty, vr.getName.asInstanceOf[Lexical].getString, expr))
        } else s"${vr.getName} has no initial value".left).sequenceU
    )
  }

  def translateDecl(decl: Declaration): String \/ List[syntax.Def] = {
    if (decl.isFunction) translateFunction(decl.asInstanceOf[Function])
    else if (decl.isData) translateData(decl.asInstanceOf[Data])
    else if (decl.isVariable) translateGlobalVariable(decl.asInstanceOf[Variable])
    else s"${decl.getName} is unsupported".left
  }

  def translateModule(module: Module): String \/ syntax.Module = {
    // TODO Deal with imports

    if (module.getBody.hasToplevels) {
      val toplevels = module.getBody.getToplevels.asScala.toList
      val defs =
        toplevels.map(toplevel => translateDecl(toplevel.getDeclaration))
      defs.sequenceU.map(_.flatten).map(syntax.Module(_))
    } else {
      s"${module.getHeader.getName} does not have any definitions".left
    }
  }
}