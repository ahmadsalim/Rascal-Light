package util.rascalwrapper

import scala.collection.JavaConverters._
import java.io.File
import java.nio.file.Files

import org.rascalmpl.ast.Declaration.{Data, Function, Variable}
import org.rascalmpl.ast.Expression.TypedVariable
import org.rascalmpl.ast.Name.Lexical
import org.rascalmpl.ast.Statement.VariableDeclaration
import org.rascalmpl.ast.{BasicType, _}
import org.rascalmpl.library.lang.rascal.syntax.RascalParser
import org.rascalmpl.parser.{ASTBuilder, Parser}
import org.rascalmpl.parser.gtd.result.out.DefaultNodeFlattener
import org.rascalmpl.parser.uptr.UPTRNodeFactory
import syntax.{BasicType => _, Module => _, Type => _, _}

import scalaz.\/
import scalaz.syntax.either._
import scalaz.std.list._
import scalaz.std.option._
import scalaz.syntax.traverse._
import scalaz.syntax.foldable._
import scalaz.syntax.monadPlus._

object RascalWrapper {
  def parseRascal(path: String): Module = {
    val parser = new RascalParser()
    val file = new File(path)
    val input = new String(Files.readAllBytes(file.toPath))
    val astbuilder = new ASTBuilder()
    val parsed = parser.parse(Parser.START_MODULE, file.toURI, input.toCharArray, new DefaultNodeFlattener(), new UPTRNodeFactory())
    astbuilder.buildModule(parsed)
  }

  def translateStatement(stmt: Statement): String \/ Expr = {
    if (stmt.isAssert || stmt.isAssertWithMessage) {
      val texpr = translateExpr(stmt.getExpression)
      texpr.map(AssertExpr)
    } else if (stmt.isAssignment) {
      val assgnop = stmt.getOperator
      if (assgnop.isDefault) {
        val assignable = stmt.getAssignable
        if (assignable.isVariable) {
          val varName = assignable.getName.asInstanceOf[Lexical].getString
          val tvarVal = translateStatement(stmt.getStatement)
          tvarVal.map(e => AssignExpr(varName, e))
        }
        else s"Unsupported assignable: $assignable".left
      }
      else s"Unsupported assignment operator: $assgnop".left
    } else if (stmt.isBreak) {
      BreakExpr.right
    } else if (stmt.isContinue) {
      ContinueExpr.right
    } else if (stmt.isEmptyStatement) {
      LocalBlockExpr(Seq(), Seq()).right
    } else if (stmt.isExpression) {
      translateExpr(stmt.getExpression)
    } else if (stmt.isFail)  {
      FailExpr.right
    } else if (stmt.isFor) {
      ???
    } else if (stmt.isIfThen || stmt.isIfThenElse) {
      ???
    } else if (stmt.isNonEmptyBlock) {
      translateStatements(stmt.getStatements.asScala.toList)
    } else if (stmt.isReturn) {
      translateStatement(stmt.getStatement).map(ReturnExpr)
    } else if (stmt.isSolve) {
      ???
    } else if (stmt.isSwitch) {
      ???
    } else if (stmt.isThrow) {
      ???
    } else if (stmt.isTry) {
      ???
    } else if (stmt.isTryFinally) { // Should finally, rethrow exceptions?
      ???
    } else if (stmt.isVisit) {
      ???
    } else if (stmt.isWhile) {
      ???
    } else s"Unsupported statement: $stmt".left
  }

  def translateStatements(stmts: List[Statement]): String \/ syntax.Expr = {
    val vardecls = stmts.takeWhile(_.isInstanceOf[VariableDeclaration])
    val reststmts = stmts.drop(vardecls.length)
    val restbeforeblock = reststmts.takeWhile(!_.isInstanceOf[VariableDeclaration])
    val restblock = reststmts.drop(restbeforeblock.length)
    val tstmtsr = restbeforeblock.traverseU(translateStatement).flatMap(es =>
      translateStatements(restblock).map(re => es :+ re))
    val tvardeclsinit = vardecls.map(_.asInstanceOf[VariableDeclaration]).traverseU { vdec =>
      val locvardecl = vdec.getDeclaration.getDeclarator
      val varstysr = translateType(locvardecl.getType)
      val parsinit = varstysr.flatMap(varsty =>
        locvardecl.getVariables.asScala.toList.traverseU { vr =>
          val vrname = vr.getName.asInstanceOf[Lexical].getString
          val initvalr =
            if (vr.hasInitial) {
              translateExpr(vr.getInitial).map(e => Some(AssignExpr(vrname, e)))
            } else None.right
          initvalr.map(initval => (Parameter(varsty, vrname), initval))
        }
      )
      parsinit
    }.map(_.flatten.unzip)
    tvardeclsinit.flatMap { case (tvardecls, tvaroptinit) =>
      val tvarinits = tvaroptinit.unite
      tstmtsr.map(tstmts => LocalBlockExpr(tvardecls, tvarinits ++ tstmts))
    }
  }

  def translateFunction(function: Function): String \/ syntax.FunDef = {
    val fundecl = function.getFunctionDeclaration
    val funsig = fundecl.getSignature
    val funrety = funsig.getType
    val tfunrety = translateType(funrety)
    val funname = funsig.getName.asInstanceOf[Lexical].getString
    val funpars = funsig.getParameters.getFormals.getFormals.asScala.toList
    val tfunpars = funpars.traverseU {
      case tvar: TypedVariable =>
        val varTyr = translateType(tvar.getType)
        val varNm = tvar.getName.asInstanceOf[Lexical].getString
        varTyr.map(varTy => Parameter(varTy, varNm))
      case e => s"Function parameter unsupported: $e".left
    }
    val funbody = fundecl.getBody
    val tfunbody = translateStatements(funbody.getStatements.asScala.toList)
    tfunrety.flatMap(rety => tfunpars.flatMap(fps => tfunbody.map(body => FunDef(rety, funname, fps, body))))
  }

  def translateData(data: Data): String \/ syntax.DataDef = {
    val dataty = data.getUser
    if (!dataty.hasParameters) {
      val datanm = dataty.getName.getNames.asScala.map(_.asInstanceOf[Lexical].getString).mkString(".")
      val variants = data.getVariants
      val tvariants = variants.asScala.toList.traverseU { variant =>
        val variantName = variant.getName.asInstanceOf[Lexical].toString
        val variantArgs = variant.getArguments
        val tvariantArgs = variantArgs.asScala.toList.traverseU { tyarg =>
          val targtyr = translateType(tyarg.getType)
          val targnm = tyarg.getName.asInstanceOf[Lexical].getString
          targtyr.map(targty => Parameter(targty, targnm))
        }
        tvariantArgs.map(targs => ConstructorDef(variantName, targs))
      }
      tvariants.map(constructors => DataDef(datanm, constructors))
    } else s"Unsupported parameterized data type: $data".left
  }

  def translateBasicType(basicTy: BasicType): String \/ syntax.Type = {
    if (basicTy.isVoid) VoidType.right
    else if (basicTy.isValue) ValueType.right
    else if (basicTy.isString) BaseType(StringType).right
    else if (basicTy.isInt) BaseType(IntType).right
    else if (basicTy.isBool) DataType("Bool").right
    else s"Unsupported basic type: $basicTy".left
  }

  def translateStructured(structuredTy: StructuredType): String \/ syntax.Type =  {
    val args = structuredTy.getArguments
    val basicTy = structuredTy.getBasicType
    if (basicTy.isList) {
      val argTy = translateType(args.get(0).getType)
      argTy.map(ListType)
    } else if (basicTy.isSet) {
      val argTy = translateType(args.get(0).getType)
      argTy.map(SetType)
    } else if (basicTy.isMap) {
      val keyTy = translateType(args.get(0).getType)
      val valTy = translateType(args.get(1).getType)
      keyTy.flatMap(keyTy =>
        valTy.map(valTy =>
          MapType(keyTy, valTy)
        )
      )
    } else s"Unsupported collection type: $structuredTy".left
  }

  def translateType(ty: Type): String \/ syntax.Type = {
    if (ty.isBasic) translateBasicType(ty.getBasic)
    else if (ty.isStructured) translateStructured(ty.getStructured)
    else if (ty.isUser) {
      val user = ty.getUser
      val names = user.getName.getNames.asScala.toList
      val name = names.map(_.asInstanceOf[Lexical].getString).mkString(".")
      if (user.hasParameters && user.getParameters.size > 0)
        s"Unsupported data-type with parameters: $name".left
      else DataType(name).right
    } else s"Unsupported type: $ty".left
  }

  def translateExpr(expr: Expression): String \/ syntax.Expr = ???

  def translateGlobalVariable(variable: Variable): String \/ List[syntax.GlobalVarDef] = {
    val vartyr = translateType(variable.getType)
    val vars = variable.getVariables.asScala.toList
    vartyr.flatMap(varty =>
      vars.traverseU(vr =>
        if (vr.hasInitial) {
          val exprr = translateExpr(vr.getInitial)
          exprr.map(expr => GlobalVarDef(varty, vr.getName.asInstanceOf[Lexical].getString, expr))
        } else s"${vr.getName} has no initial value".left)
    )
  }

  def translateDecl(decl: Declaration): String \/ List[syntax.Def] = {
    if (decl.isFunction) translateFunction(decl.asInstanceOf[Function]).map(_.point[List])
    else if (decl.isData) translateData(decl.asInstanceOf[Data]).map(_.point[List])
    else if (decl.isVariable) translateGlobalVariable(decl.asInstanceOf[Variable])
    else s"Unsupported declaration: $decl".left
  }

  def translateModule(module: Module): String \/ syntax.Module = {
    // TODO Deal with imports

    if (module.getBody.hasToplevels) {
      val toplevels = module.getBody.getToplevels.asScala.toList
      val defs =
        toplevels.traverseU(toplevel => translateDecl(toplevel.getDeclaration))
      defs.map(_.flatten).map(syntax.Module(_))
    } else {
      s"${module.getHeader.getName} does not have any definitions".left
    }
  }
}