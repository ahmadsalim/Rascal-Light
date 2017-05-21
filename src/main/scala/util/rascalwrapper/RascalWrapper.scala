package util.rascalwrapper

import java.io.File
import java.nio.file.Files

import org.bitbucket.inkytonik.kiama.rewriting.Rewriter
import org.rascalmpl.ast.Declaration.{Data, Function, Variable}
import org.rascalmpl.ast.Expression.TypedVariable
import org.rascalmpl.ast.Statement.VariableDeclaration
import org.rascalmpl.ast.{Assignable, BasicType, Case, _}
import org.rascalmpl.library.lang.rascal.syntax.RascalParser
import org.rascalmpl.parser.gtd.exception.ParseError
import org.rascalmpl.parser.gtd.result.out.DefaultNodeFlattener
import org.rascalmpl.parser.uptr.UPTRNodeFactory
import org.rascalmpl.parser.{ASTBuilder, Parser}
import syntax.{BasicType => _, ModuleDef => _, Type => _, _}

import scala.collection.JavaConverters._
import scala.util.Try
import scalaz.\/
import scalaz.std.list._
import scalaz.std.option._
import scalaz.syntax.either._
import scalaz.syntax.monadPlus._
import scalaz.syntax.traverse._

// TODO Consider using pickling if parsing and translation is a bit slow
object RascalWrapper {
  private
  var varCounter = 0

  private
  def qualifiedNameToString(qn: QualifiedName) = qn.getNames.asScala.map(nameToString).mkString(".")

  private
  def literalToString(stringConstant: StringConstant): String = {
    stringConstant match {
      case lexical: StringConstant.Lexical => lexical.getString
    }
  }

  private
  def literalToInteger(integerLiteral: IntegerLiteral): Int = {
    if (integerLiteral.isDecimalIntegerLiteral) {
      integerLiteral.getDecimal match {
        case lexical: DecimalIntegerLiteral.Lexical => lexical.getString.toInt
      }
    } else if (integerLiteral.isHexIntegerLiteral) {
      integerLiteral.getHex match {
        case lexical: HexIntegerLiteral.Lexical => lexical.getString.toInt
      }
    } else {
      integerLiteral.getOctal match {
        case lexical: OctalIntegerLiteral.Lexical => lexical.getString.toInt
      }
    }
  }

  private
  def nameToString(name: org.rascalmpl.ast.Name): String = {
    name match {
      case lexical: Name.Lexical => lexical.getString
    }
  }

  def parseRascal(path: String): String \/ Module = {
    val parser = new RascalParser()
    val file = new File(path)
    val input = new String(Files.readAllBytes(file.toPath))
    val astbuilder = new ASTBuilder()
    val parsed = \/.fromTryCatchNonFatal {
      parser.parse(Parser.START_MODULE, file.toURI, input.toCharArray, new DefaultNodeFlattener(), new UPTRNodeFactory(false))
    }
    parsed.leftMap {
      case parseErr : ParseError => parseErr.toString
      case err => err.getMessage
    }.map(astbuilder.buildModule)
  }


  private
  def translateStarPattern(pattern: Expression): String \/ StarPatt = {
    if (pattern.isMultiVariable) {
      val varName = qualifiedNameToString(pattern.getQualifiedName)
      ArbitraryPatt(varName).right
    } else {
      translatePattern(pattern).map(OrdinaryPatt)
    }
  }

  private
  def translatePattern(pattern: Expression): String \/ Patt = {
    if (pattern.isCallOrTree) {
      val caller = pattern.getExpression
      val args = pattern.getArguments.asScala.toList
      val subpatterns = args.traverseU(translatePattern)
      val consName = qualifiedNameToString(caller.getQualifiedName)
      subpatterns.map(ConstructorPatt(consName,_))
    } else if (pattern.isLiteral) {
      val lit = pattern.getLiteral
      if (lit.isInteger) {
        BasicPatt(IntLit(literalToInteger(lit.getIntegerLiteral))).right
      } else if (lit.isString && lit.getStringLiteral.isNonInterpolated) {
        BasicPatt(StringLit(literalToString(lit.getStringLiteral.getConstant))).right
      } else {
        s"Unsupported literal: $lit".left
      }
    } else if (pattern.isQualifiedName) {
      val varName = qualifiedNameToString(pattern.getQualifiedName)
      if (varName == "_") IgnorePatt.right else VarPatt(varName).right
    } else if (pattern.isDescendant) {
      val innerPatt = translatePattern(pattern.getPattern)
      innerPatt.map(DescendantPatt)
    } else if (pattern.isList) {
      val innerPats = pattern.getElements0.asScala.toList
      innerPats.traverseU(translateStarPattern).map(ListPatt)
    } else if (pattern.isSet) {
      val innerPats = pattern.getElements0.asScala.toList
      innerPats.traverseU(translateStarPattern).map(SetPatt)
    } else if (pattern.isNegation) {
      val innerPat = pattern.getArgument
      translatePattern(innerPat).map(NegationPatt)
    } else if (pattern.isVariableBecomes || pattern.isTypedVariable || pattern.isTypedVariableBecomes) {
      val varName = nameToString(pattern.getName)
      val varType = if (pattern.hasType) translateType(pattern.getType) else ValueType.right
      val varExpr = if (pattern.hasPattern) translatePattern(pattern.getPattern) else VarPatt(varName).right
      varType.flatMap(ty => varExpr.map(patt => LabelledTypedPatt(ty, varName, patt)))
    } else {
      s"Unsupported pattern: $pattern".left
    }
  }

  private
  def translateEnum(enum: Expression): String \/ Enum = {
    if (enum.isMatch) {
      translatePattern(enum.getPattern).flatMap(patt =>
        translateExpression(enum.getExpression).map(MatchAssign(patt, _)))
    } else if (enum.isEnumerator) {
      val pattern = enum.getPattern
      val expr = enum.getExpression
      if (pattern.isQualifiedName) {
        val name = qualifiedNameToString(pattern.getQualifiedName)
        translateExpression(expr).map(EnumAssign(name, _))
      } else s"Unsupported pattern in enumeration: $pattern".left
    } else {
      s"Unsupported enumeration expression: $enum".left
    }
  }

  private
  def translateCases(cases: List[Case], inSwitch: Boolean): String \/ List[syntax.Case] = {
    cases.traverseU { cas =>
      (if (cas.isPatternWithAction) {
        val patternWithAction = cas.getPatternWithAction
        val pattern = patternWithAction.getPattern
        if (patternWithAction.isArbitrary) {
          if (inSwitch) {
            val statement = patternWithAction.getStatement
            translatePattern(pattern).flatMap(patt => translateStatement(statement).map(syntax.Case(patt, _)))
          } else {
            s"Unsupported non-replacement pattern with action in visit: $pattern".left
          }
        } else {
          val replacing = patternWithAction.getReplacement
          if (replacing.hasConditions) {
            s"Unsupported conditioned replacement pattern with action: $replacing".left
          } else {
            translatePattern(pattern).flatMap(patt =>
              translateExpression(replacing.getReplacementExpression).map(syntax.Case(patt, _)))
          }
        }
      } else {
        translateStatement(cas.getStatement).map(syntax.Case(IgnorePatt, _))
      }) : String \/ syntax.Case
    }
  }

  private
  def translateStatement(stmt: Statement): String \/ Expr = {
    if (stmt.isAssert || stmt.isAssertWithMessage) {
      val texpr = translateExpression(stmt.getExpression)
      texpr.map(AssertExpr)
    } else if (stmt.isAssignment) {
      val assgnop = stmt.getOperator
      val tvarVal = translateStatement(stmt.getStatement)
     if (assgnop.isDefault) {
        val assignable = stmt.getAssignable
        val target = translateAssignable(assignable)
        tvarVal.flatMap(e => target.map(t =>  AssignExpr(t, e)))
      }
      else s"Unsupported assignment operator: $assgnop".left
    } else if (stmt.isBreak) {
      BreakExpr.right
    } else if (stmt.isContinue) {
      ContinueExpr.right
    } else if (stmt.isEmptyStatement) {
      LocalBlockExpr(Seq(), Seq()).right
    } else if (stmt.isExpression) {
      translateExpression(stmt.getExpression)
    } else if (stmt.isFail)  {
      FailExpr.right
    } else if (stmt.isFor) {
      val gens = stmt.getGenerators
      val body = stmt.getBody
      if (gens.size == 1) {
        translateEnum(gens.get(0)).flatMap(enum => translateStatement(body).map(ForExpr(enum, _)))
      } else { s"Unsupported multiple-generator for-loop: $gens".left }
    } else if (stmt.isIfThen || stmt.isIfThenElse) {
      if (stmt.getConditions.size == 1) {
        val tcondr = translateExpression(stmt.getConditions.get(0))
        val thenbr = translateStatement(stmt.getThenStatement)
        val elsebr = if (stmt.hasElseStatement) translateStatement(stmt.getElseStatement) else LocalBlockExpr(Seq(), Seq()).right
        tcondr.flatMap(cond => thenbr.flatMap(thenb => elsebr.map(elseb => IfExpr(cond, thenb, elseb))))
      } else {
        s"Only one condition supported in if loop: $stmt".left
      }
    } else if (stmt.isNonEmptyBlock) {
      translateStatements(stmt.getStatements.asScala.toList)
    } else if (stmt.isReturn) {
      translateStatement(stmt.getStatement).map(ReturnExpr)
    } else if (stmt.isSolve) {
      if (stmt.getBound.isEmpty) {
        val vars = stmt.getVariables.asScala.toList.map(qualifiedNameToString)
        val body = stmt.getBody
        translateStatement(body).map(SolveExpr(vars, _))
      } else {
       s"Unsupported bounded solve-statement: $stmt".left
      }
    } else if (stmt.isSwitch) {
      val subject = stmt.getExpression
      val cases = stmt.getCases.asScala.toList
      translateExpression(subject).flatMap(subj => translateCases(cases, inSwitch = true).map(SwitchExpr(subj, _)))
    } else if (stmt.isThrow) {
      val valu = stmt.getStatement
      translateStatement(valu).map(ThrowExpr)
    } else if (stmt.isTry || stmt.isTryFinally) {
      val trybodyr = translateStatement(stmt.getBody)
      // TO DO binding handlers seem to not return any value unlike semantics?
      val handlers = stmt.getHandlers.asScala.toList
      val defaultHandler = handlers.find(_.isDefault)
      val bindingHandlers = handlers.filter(_.isBinding)
      val catchVar = s"catch$$$varCounter"
      val defaultVar = s"default$$$varCounter"
      varCounter += 1
      val handlingCases = bindingHandlers.traverseU { ch =>
        val pattr = translatePattern(ch.getPattern)
        val bodyr = translateStatement(ch.getBody)
        pattr.flatMap(patt => bodyr.map(body => syntax.Case(patt, body)))
      }
      val defaultBody = defaultHandler.fold[String \/ Expr](ThrowExpr(VarExpr(catchVar)).right)(ch => translateStatement(ch.getBody))
      val allCases = handlingCases.flatMap(cs => defaultBody.map(body => cs ++ List(syntax.Case(VarPatt(defaultVar), body))))
      val trycatch = trybodyr.flatMap(trybody => allCases.map(cs => TryCatchExpr(trybody, catchVar, SwitchExpr(VarExpr(catchVar), cs))))
      if (stmt.hasFinallyBody) {
        val finallybodyr = translateStatement(stmt.getFinallyBody)
        trycatch.flatMap(tc => finallybodyr.map(fb => TryFinallyExpr(tc, fb)))
      } else trycatch
    } else if (stmt.isVisit) {
      val visit = stmt.getVisit
      translateVisit(visit)
    } else if (stmt.isWhile) {
      if (stmt.getConditions.size != 1) s"Only one condition supported in while loop: $stmt".left
      else {
        val tcondr = translateExpression(stmt.getConditions.get(0))
        val tbodyr = translateStatement(stmt.getBody)
        tcondr.flatMap(cond => tbodyr.map(body => WhileExpr(cond, body)))
      }
    } else s"Unsupported statement: $stmt".left
  }

  private
  def translateAssignable(assignable: Assignable): String \/ syntax.Assignable = {
    if (assignable.isVariable) {
      val varName = qualifiedNameToString(assignable.getQualifiedName)
      VarAssgn(varName).right
    } else if (assignable.isFieldAccess) {
      val target = assignable.getReceiver
      val fieldName = nameToString(assignable.getField)
      translateAssignable(target).map(FieldAccAssgn(_, fieldName))
    } else if (assignable.isSubscript) {
      val target = assignable.getReceiver
      val ekey = assignable.getSubscript
      translateAssignable(target).flatMap(t => translateExpression(ekey).map(MapUpdAssgn(t, _)))
    } else if (assignable.isBracket) {
      translateAssignable(assignable.getArg)
    } else {
      s"Unsupported assignable: $assignable".left
    }
  }

  private
  def translateVisit(visit: Visit): String \/ Expr = {
      val strat = {
        if (visit.isGivenStrategy) {
          val strategy = visit.getStrategy
          if (strategy.isBottomUp) BottomUp
          else if (strategy.isBottomUpBreak) BottomUpBreak
          else if (strategy.isInnermost) Innermost
          else if (strategy.isTopDown) TopDown
          else if (strategy.isTopDownBreak) TopDownBreak
          else /* strategy.isOutermost */ Outermost
        } else TopDown
      }
      val subject = visit.getSubject
      val cases = visit.getCases.asScala.toList
      translateExpression(subject).flatMap(subj =>
        translateCases(cases, inSwitch = false).map(cs => VisitExpr(strat, subj, cs)))
  }

  private
  def translateStatements(stmts: List[Statement]): String \/ syntax.Expr = {
    val vardecls = stmts.takeWhile(_.isInstanceOf[VariableDeclaration])
    val reststmts = stmts.drop(vardecls.length)
    val restbeforeblock = reststmts.takeWhile(!_.isInstanceOf[VariableDeclaration])
    val restblock = reststmts.drop(restbeforeblock.length)
    val tstmtsr = restbeforeblock.traverseU(translateStatement).flatMap(es =>
      if (restblock.isEmpty) es.right else translateStatements(restblock).map(re => es :+ re))
    val tvardeclsinit = vardecls.map(_.asInstanceOf[VariableDeclaration]).traverseU { vdec =>
      val locvardecl = vdec.getDeclaration.getDeclarator
      val varstysr = translateType(locvardecl.getType)
      val parsinit = varstysr.flatMap(varsty =>
        locvardecl.getVariables.asScala.toList.traverseU { vr =>
          val vrname = nameToString(vr.getName)
          val initvalr =
            if (vr.hasInitial) {
              translateExpression(vr.getInitial).map(e => Some(AssignExpr(VarAssgn(vrname), e)))
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

  private
  def translateFunction(function: Function): String \/ syntax.Def = {
    val fundecl = function.getFunctionDeclaration
    val funsig = fundecl.getSignature
    val funrety = funsig.getType
    val tfunrety = translateType(funrety)
    val funname = nameToString(funsig.getName)
    val funpars = funsig.getParameters.getFormals.getFormals.asScala.toList
    val tfunpars = funpars.traverseU {
      case tvar: TypedVariable =>
        val varTyr = translateType(tvar.getType)
        val varNm = nameToString(tvar.getName)
        varTyr.map(varTy => Parameter(varTy, varNm))
      case e => s"Function parameter unsupported: $e".left
    }
    if (fundecl.isDefault) {
      val funbody = fundecl.getBody
      val tfunbody = translateStatements(funbody.getStatements.asScala.toList)
      if (funsig.hasModifiers && funsig.getModifiers.getModifiers.asScala.exists(_.isTest)) {
        tfunbody.map(body => TestDef(funname, body))
      } else {
        tfunrety.flatMap(rety => tfunpars.flatMap(fps => tfunbody.map(body => FunDef(rety, funname, fps, body))))
      }
    } else if (fundecl.isExpression) {
      val funexpr = fundecl.getExpression
      val tfunexpr = translateExpression(funexpr)
      if (funsig.hasModifiers && funsig.getModifiers.getModifiers.asScala.exists(_.isTest)) {
        tfunexpr.map(body => TestDef(funname, body))
      } else {
        tfunrety.flatMap(rety => tfunpars.flatMap(fps => tfunexpr.map(body => FunDef(rety, funname, fps, body))))
      }
    } else {
      s"Unsupported function declaration: $fundecl".left
    }
  }

  private
  def translateData(data: Data): String \/ syntax.DataDef = {
    val dataty = data.getUser
    if (!dataty.hasParameters) {
      val datanm = qualifiedNameToString(dataty.getName)
      val variants = data.getVariants
      val tvariants = variants.asScala.toList.traverseU { variant =>
        val variantName = nameToString(variant.getName)
        val variantArgs = variant.getArguments
        val tvariantArgs = variantArgs.asScala.toList.zipWithIndex.traverseU { case (tyarg, idx) =>
          val targtyr = translateType(tyarg.getType)
          val targnm = if (tyarg.hasName) nameToString(tyarg.getName) else s"arg$idx"
          targtyr.map(targty => Parameter(targty, targnm))
        }
        tvariantArgs.map(targs => ConstructorDef(variantName, targs))
      }
      tvariants.map(constructors => DataDef(datanm, constructors))
    } else s"Unsupported parameterized data type: $data".left
  }

  private
  def translateBasicType(basicTy: BasicType): String \/ syntax.Type = {
    if (basicTy.isVoid) VoidType.right
    else if (basicTy.isValue) ValueType.right
    else if (basicTy.isString) BaseType(StringType).right
    else if (basicTy.isInt) BaseType(IntType).right
    else if (basicTy.isBool) DataType("Bool").right
    else s"Unsupported basic type: $basicTy".left
  }

  private
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

  private
  def translateType(ty: Type): String \/ syntax.Type = {
    if (ty.isBasic) translateBasicType(ty.getBasic)
    else if (ty.isStructured) translateStructured(ty.getStructured)
    else if (ty.isUser) {
      val user = ty.getUser
      val names = user.getName.getNames.asScala.toList
      val name = names.map(nameToString).mkString(".")
      if (user.hasParameters && user.getParameters.size > 0)
        s"Unsupported data-type with parameters: $name".left
      else DataType(name).right
    } else s"Unsupported type: $ty".left
  }

  def literalToBool(boolLit: BooleanLiteral): syntax.Expr = {
    boolLit match {
      case lexical : BooleanLiteral.Lexical =>
        val lexicalString = lexical.getString
        lexicalString match {
          case "true" => ConstructorExpr("true", List())
          case "false" => ConstructorExpr("false", List())
        }
    }
  }

  private
  def translateExpression(expr: Expression): String \/ syntax.Expr = {
    if (expr.isQualifiedName) {
      val varName = qualifiedNameToString(expr.getQualifiedName)
      VarExpr(varName).right
    } else if (expr.isLiteral) {
      val lit = expr.getLiteral
      if (lit.isInteger) {
        val intlit = lit.getIntegerLiteral
        BasicExpr(IntLit(literalToInteger(intlit))).right
      } else if (lit.isString) {
        val stringLit = lit.getStringLiteral
        if (stringLit.isInterpolated) {
          translateExpression(stringLit.getExpression).map(e => FunCallExpr("toString", List(e)))
        } else if (stringLit.isNonInterpolated) {
          BasicExpr(StringLit(literalToString(stringLit.getConstant))).right
        } else {
          s"Unsupported string literal: $stringLit".left
        }
      } else if (lit.isBoolean) {
        val boolLit = lit.getBooleanLiteral
        literalToBool(boolLit).right
      } else {
        s"Unsupported literal: $lit".left
      }
    } else if (expr.isCallOrTree) {
      val caller = expr.getExpression
      val args = expr.getArguments.asScala.toList
      val subexpressions = args.traverseU(translateExpression)
      subexpressions.map(FunCallExpr(qualifiedNameToString(caller.getQualifiedName), _))
    } else if (expr.isNegation || expr.isNegative) {
      val inner = expr.getArgument
      val opName = if (expr.isNegation) "!" else /* expr.isNegative */ "-"
      translateExpression(inner).map(UnaryExpr(opName,_))
    } else if (expr.isAddition) {
      val lhs = expr.getLhs
      val rhs = expr.getRhs
      if (rhs.isMap) {
        val mappings = rhs.getMappings.asScala.toList
        if (mappings.size == 1) {
          val upd = mappings.head
          val key = upd.getFrom
          val valu = upd.getTo
          translateExpression(lhs).flatMap(map =>
            translateExpression(key).flatMap(k => translateExpression(valu).map(v => MapUpdExpr(map, k, v))
          ))
        } else {
          s"Unsupported update with multiple keys: $mappings".left
        }
      } else {
        translateExpression(lhs).flatMap(l => translateExpression(rhs).map(r => BinaryExpr(l, "+", r)))
      }
    } else if(expr.isAnd || expr.isOr ||
              expr.isEquals || expr.isNonEquals ||
              expr.isImplication || expr.isEquivalence || expr.isIn || expr.isNotIn ||
              expr.isLessThan || expr.isGreaterThan ||
              expr.isGreaterThanOrEq || expr.isLessThanOrEq ||
              expr.isDivision  || expr.isSubtraction || expr.isProduct
              || expr.isRemainder) {
      val lhs = expr.getLhs
      val rhs = expr.getRhs
      val opName = {
        if (expr.isAnd) "&&"
        else if (expr.isOr) "||"
        else if (expr.isEquals) "=="
        else if (expr.isNonEquals) "!="
        else if (expr.isImplication) "==>"
        else if (expr.isEquivalence) "<==>"
        else if (expr.isIn) "in"
        else if (expr.isNotIn) "notin"
        else if (expr.isLessThan) "<"
        else if (expr.isGreaterThan) ">"
        else if (expr.isLessThanOrEq) "<="
        else if (expr.isGreaterThanOrEq) ">="
        else if (expr.isDivision) "/"
        else if (expr.isSubtraction) "-"
        else if (expr.isRemainder) "%"
        else /* expr.isProduct */ "*"
      }
      translateExpression(lhs).flatMap(l => translateExpression(rhs).map(r => BinaryExpr(l, opName, r)))
    } else if (expr.isList) {
      val elems = expr.getElements0.asScala.toList
      elems.traverseU(translateExpression).map(ListExpr)
    } else if (expr.isSet) {
      val elems = expr.getElements0.asScala.toList
      elems.traverseU(translateExpression).map(SetExpr)
    } else if (expr.isMap) {
      val mappings = expr.getMappings.asScala.toList.map(mp => mp.getFrom -> mp.getTo)
      mappings.traverseU {
        case (e1, e2) => translateExpression(e1).flatMap(e1 => translateExpression(e2).map(e1 -> _))
      }.map(MapExpr)
    } else if (expr.isSubscript) {
      val target = expr.getExpression
      val subscrs = expr.getSubscripts
      if (subscrs.size == 1) {
        val subscr = subscrs.get(0)
        translateExpression(target).flatMap(t =>
          translateExpression(subscr).map(sub => MapLookupExpr(t, sub))
        )
      } else { s"Unsupported multiple subscripts: $subscrs".left }
    } else if (expr.isVisit) {
      translateVisit(expr.getVisit)
    } else if (expr.isNonEmptyBlock) {
      translateStatements(expr.getStatements.asScala.toList)
    } else if (expr.isBracket) {
      translateExpression(expr.getExpression)
    } else if (expr.isFieldAccess) {
      val target = expr.getExpression
      val fieldName = nameToString(expr.getField)
      translateExpression(target).map(FieldAccExpr(_, fieldName))
    } else if (expr.isIfThenElse) {
      val cond = expr.getCondition
      val thenB = expr.getThenExp
      val elseB = expr.getElseExp
      translateExpression(cond).flatMap(c =>
        translateExpression(thenB).flatMap(th => translateExpression(elseB).map(IfExpr(c, th, _)))
      )
    } else {
      s"Unsupported expression $expr".left
    }
  }

  private
  def translateGlobalVariable(variable: Variable): String \/ List[syntax.GlobalVarDef] = {
    val vartyr = translateType(variable.getType)
    val vars = variable.getVariables.asScala.toList
    vartyr.flatMap(varty =>
      vars.traverseU(vr =>
        if (vr.hasInitial) {
          val exprr = translateExpression(vr.getInitial)
          exprr.map(expr => GlobalVarDef(varty, nameToString(vr.getName), expr))
        } else s"${vr.getName} has no initial value".left)
    )
  }

  private
  def translateDecl(decl: Declaration): String \/ List[syntax.Def] = {
    if (decl.isFunction) translateFunction(decl.asInstanceOf[Function]).map(_.point[List])
    else if (decl.isData) translateData(decl.asInstanceOf[Data]).map(_.point[List])
    else if (decl.isVariable) translateGlobalVariable(decl.asInstanceOf[Variable])
    else s"Unsupported declaration: $decl".left
  }

  private
  def resolveConstructorCalls(consNames: Set[ConsName], df: Def): Def = {
    val rewriteConsNames = Rewriter.rule[Expr] {
      case e@FunCallExpr(functionName, args) if consNames.contains(functionName) => ConstructorExpr(functionName, args)
    }
    Rewriter.rewrite(Rewriter.outermost("Rewrite Constructors", rewriteConsNames))(df)
  }

  def translateModule(module: Module): String \/ syntax.ModuleDef = {
    // TODO Deal with imports

    if (module.getBody.hasToplevels) {
      val toplevels = module.getBody.getToplevels.asScala.toList
      val defs =
        toplevels.traverseU(toplevel => translateDecl(toplevel.getDeclaration))
      val tmodr = defs.map(_.flatten).map(syntax.ModuleDef(_))
      tmodr.map { tmod =>
        val constructorNames = tmod.defs.flatMap {
          case dd: DataDef => dd.constructors.map(_.name)
          case _ => Seq()
        }.toSet
        syntax.ModuleDef(tmod.defs.map(df => resolveConstructorCalls(constructorNames, df)))
      }
    } else {
      s"${module.getHeader.getName} does not have any definitions".left
    }
  }

  def loadModuleFromFile(path: String): String \/ syntax.ModuleDef = {
    parseRascal(path).flatMap(translateModule)
  }
}