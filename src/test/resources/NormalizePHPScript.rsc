/**
 * Normalization procedure for PHP scripts
 * Port from https://github.com/cwi-swat/php-analysis
 */
module NormalizePHPScript

public data OptionExpr = someExpr(Expr expr) | noExpr();

public data OptionName = someName(Name name) | noName();

public data OptionElse = someElse(Else e) | noElse();

public data ActualParameter = actualParameter(Expr expr, bool byRef);

public data Const = const(str name, Expr constValue);

public data ArrayElement = arrayElement(OptionExpr key, Expr val, bool byRef);

public data NameNominal = n_isset() | n_exit() | n_die() | n_print() | n_unset() | n_empty() | n_eval() | n_other();

public data Name = name(NameNominal n);

public data NameOrExpr = nameE(Name name) | expr(Expr expr);

public data CastType = intTy() | boolTy() | floatTy() | stringTy() | arrayTy() | objectTy() | unsetTy();

public data ClosureUse = closureUse(Expr varName, bool byRef);

public data IncludeType = includeTy() | includeOnceTy() | requireTy() | requireOnceTy();

// NOTE: In PHP, yield is a statement, but it can also be used as an expression.
// To handle this, we just treat it as an expression. The parser does this as well.
// TODO: listAssign is deprecated and will be removed in the future, this is now
// given as an assignment into a listExpr
public data Expr
	= array(list[ArrayElement] items)
	| fetchArrayDim(Expr var, OptionExpr dim)
	| fetchClassConst(NameOrExpr className, str constantName)
	| assign(Expr assignTo, Expr assignExpr)
	| assignWOp(Expr assignTo, Expr assignExpr, Op operation)
	| listAssign(list[OptionExpr] assignsTo, Expr assignExpr)
	| refAssign(Expr assignTo, Expr assignExpr)
	| binaryOperation(Expr left, Expr right, Op operation)
	| unaryOperation(Expr operand, Op operation)
	| new(NameOrExpr className, list[ActualParameter] parameters)
	| cast(CastType castType, Expr expr)
	| clone(Expr expr)
	| closure(list[Stmt] statements, list[Param] params, list[ClosureUse] closureUses, bool byRef, bool static)
	| fetchConst(Name name)
	| empty(Expr expr)
	| suppress(Expr expr)
	| eval(Expr expr)
	| exit(OptionExpr exitExpr)
	| call(NameOrExpr funName, list[ActualParameter] parameters)
	| methodCall(Expr target, NameOrExpr methodName, list[ActualParameter] parameters)
	| staticCall(NameOrExpr staticTarget, NameOrExpr methodName, list[ActualParameter] parameters)
	| include(Expr expr, IncludeType includeType)
	| instanceOf(Expr expr, NameOrExpr toCompare)
	| isSet(list[Expr] exprs)
	| printE(Expr expr)
	| propertyFetch(Expr target, NameOrExpr propertyName)
	| shellExec(list[Expr] parts)
	| ternary(Expr cond, OptionExpr ifBranch, Expr elseBranch)
	| staticPropertyFetch(NameOrExpr className, NameOrExpr propertyName)
	| scalar(Scalar scalarVal)
	| var(NameOrExpr varName)
	| yield(OptionExpr keyExpr, OptionExpr valueExpr)
	| yieldFrom(Expr fromExpr)
	| listExpr(list[OptionExpr] listExprs)
	;


public data Op = bitwiseAnd() | bitwiseOr() | bitwiseXor() | concat() | div()
			   | minus() | \mod() | mul() | plus() | rightShift() | leftShift()
			   | booleanAnd() | booleanOr() | booleanNot() | bitwiseNot()
			   | gt() | geq() | logicalAnd() | logicalOr() | logicalXor()
			   | notEqual() | notIdentical() | postDec() | preDec() | postInc()
			   | preInc() | lt() | leq() | unaryPlus() | unaryMinus()
			   | equal() | identical() | pow() | coalesce() | spaceship() ;

public data Param = param(str paramName,
						  OptionExpr paramDefault,
						  OptionName paramType,
						  bool byRef);

public data Scalar
	= classConstant()
	| dirConstant()
	| fileConstant()
	| funcConstant()
	| lineConstant()
	| methodConstant()
	| namespaceConstant()
	| traitConstant()
	| integer(int intVal)
	| string(str strVal)
	| encapsed(list[Expr] parts)
	;

public data HTMLNominal = no_html_text() | html_text();

public data Stmt
	= \break(OptionExpr breakExpr)
	| classDef(ClassDef classDef)
	| constE(list[Const] consts)
	| \continue(OptionExpr continueExpr)
	| declare(list[Declaration] decls, list[Stmt] body)
	| do(Expr cond, list[Stmt] body)
	| echo(list[Expr] exprs)
	| exprstmt(Expr expr)
	| \for(list[Expr] inits, list[Expr] conds, list[Expr] exprs, list[Stmt] body)
	| foreach(Expr arrayExpr, OptionExpr keyvar, bool byRef, Expr asVar, list[Stmt] body)
	| function(str name, bool byRef, list[Param] params, list[Stmt] body)
	| global(list[Expr] exprs)
	| goto(str label)
	| haltCompiler(str remainingText)
	| \if(Expr cond, list[Stmt] body, list[ElseIf] elseIfs, OptionElse elseClause)
	| inlineHTML(HTMLNominal htmlText)
	| interfaceDef(InterfaceDef interfaceDef)
	| traitDef(TraitDef traitDef)
	| label(str labelName)
	| namespace(OptionName nsName, list[Stmt] body)
	| namespaceHeader(Name namespaceName)
	| \return(OptionExpr returnExpr)
	| static(list[StaticVar] vars)
	| \switch(Expr cond, list[Case] cases)
	| \throw(Expr expr)
	| tryCatch(list[Stmt] body, list[Catch] catches)
	| tryCatchFinally(list[Stmt] body, list[Catch] catches, list[Stmt] finallyBody)
	| unset(list[Expr] unsetVars)
	| useE(list[Use] uses)
	| \while(Expr cond, list[Stmt] body)
	| emptyStmt()
	| block(list[Stmt] body)
	;

public data Declaration = declaration(str key, Expr val);

public data Catch = \catch(Name xtype, str varName, list[Stmt] body);

public data Case = \case(OptionExpr cond, list[Stmt] body);

public data ElseIf = elseIf(Expr cond, list[Stmt] body);

public data Else = \else(list[Stmt] body);

public data Use = use(Name importName, OptionName asName);

public data ClassItem
	= propertyCI(set[Modifier] modifiers, list[Property] prop)
	| constCI(list[Const] consts)
	| method(str name, set[Modifier] modifiers, bool byRef, list[Param] params, list[Stmt] body)
	| traitUse(list[Name] traits, list[Adaptation] adaptations)
	;

public data Adaptation
	= traitAlias(OptionName traitName, str methName, set[Modifier] newModifiers, OptionName newName)
	| traitPrecedence(OptionName traitName, str methName, set[Name] insteadOf)
	;

public data Property = property(str propertyName, OptionExpr defaultValue);

public data Modifier = publicM() | privateM() | protectedM() | staticM() | abstractM() | finalM();

public data ClassDef = class(str className,
							 set[Modifier] modifiers,
							 OptionName extends,
							 list[Name] implements,
							 list[ClassItem] members);

public data InterfaceDef = interface(str interfaceName,
									list[Name] extends,
									list[ClassItem] members);

public data TraitDef = trait(str traitName, list[ClassItem] members);

public data StaticVar = staticVar(str name, OptionExpr defaultValue);

public data Script = script(list[Stmt] body) | errscript(str err);

public Script oldNamespaces(Script s) {
	solve(s) {
		s = visit(s) {
			case namespaceHeader(Name nn) => namespace(someName(nn), [])
		}
	}
	return s;
}

public Stmt createIf(ElseIf e, OptionElse oe) {
    switch (e) {
      case elseIf(Expr cond, list[Stmt] body): return \if(cond, body, [], oe);
    }
}

public Script normalizeIf(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case Stmt i:\if(cond,body,elseifs,els) => ({
				if (size(elseifs) > 0) {
					workingElse = els;
					for (e <- reverse(elseifs)) {
						newIf = createIf(e, workingElse);
						workingElse = someElse(\else([newIf]));
					}
					\if(cond,body,[],workingElse);
				} else i;
			})
		}
	}
	return s;
}

// Good as example
public Script flattenBlocks(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case list[Stmt] stmtList: [*xs,block(list[Stmt] ys),*zs] => xs + ys + zs
		}
	}
	return s;
}

public Script discardEmpties(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case list[Stmt] stmtList: [*xs,emptyStmt(),*zs] => xs + zs
		}
	}
	return s;
}

public Script useBuiltins(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case call(nameE(name(n_isset())),params) => ({
			   list[Expr] es = [];
			   for (ap <- params)
			     switch(ap) {
			       case actualParameter(e,_,_):
			         es = es + e;
			       case _:;
			     };
			   isSet(es);
			})

			case call(nameE(name(n_exit())),[]) => exit(noExpr(), true)

			case call(nameE(name(n_exit())),[actualParameter(e,_,_)]) => exit(someExpr(e), true)

			case call(nameE(name(n_die())),[]) => exit(noExpr(), false)

			case call(nameE(name(n_die())),[actualParameter(e,_,_)]) => exit(someExpr(e), false)

			case call(nameE(name(n_print())),[actualParameter(e,_,_)]) => printE(e)

			case exprstmt(call(nameE(name(n_unset())),params)) => ({
			   list[Expr] es = [];
			   for (ap <- params)
			     switch(ap) {
			       case actualParameter(e,_,_):
			         es = es + e;
			       case _:;
			     };
			   unset(es);
			})

			case call(nameE(name(n_empty())),[actualParameter(e,_,_)]) => empty(e)

			case call(nameE(name(n_eval())),[actualParameter(e,_,_)]) => eval(e)
		}
	}
	return s;
}

public Script discardHTML(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case inlineHTML(_) => inlineHTML(no_html_text())
		}
	}
	return s;
}

public Script normalizeScript(Script sc) {
		sc = oldNamespaces(sc);
		sc = normalizeIf(sc);
		sc = flattenBlocks(sc);
		sc = discardEmpties(sc);
		sc = useBuiltins(sc);
		sc = discardHTML(sc);
		return sc;
}
