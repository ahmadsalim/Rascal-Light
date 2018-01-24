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

public data Name = name(str name);

public data NameOrExpr = name(Name name) | expr(Expr expr);

public data CastType = \int() | \bool() | float() | string() | array() | object() | unset();

public data ClosureUse = closureUse(Expr varName, bool byRef);

public data IncludeType = include() | includeOnce() | require() | requireOnce();

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
	| print(Expr expr)
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
	| float(real realVal)
	| integer(int intVal)
	| string(str strVal)
	| encapsed(list[Expr] parts)
	;

public data Stmt
	= \break(OptionExpr breakExpr)
	| classDef(ClassDef classDef)
	| const(list[Const] consts)
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
	| inlineHTML(str htmlText)
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
	| use(list[Use] uses)
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
	= property(set[Modifier] modifiers, list[Property] prop)
	| constCI(list[Const] consts)
	| method(str name, set[Modifier] modifiers, bool byRef, list[Param] params, list[Stmt] body)
	| traitUse(list[Name] traits, list[Adaptation] adaptations)
	;

public data Adaptation
	= traitAlias(OptionName traitName, str methName, set[Modifier] newModifiers, OptionName newName)
	| traitPrecedence(OptionName traitName, str methName, set[Name] insteadOf)
	;

public data Property = property(str propertyName, OptionExpr defaultValue);

public data Modifier = \public() | \private() | protected() | static() | abstract() | final();

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

public Stmt createIf(ElseIf e:elseIf(Expr cond, list[Stmt] body), OptionElse oe) {
	return \if(cond, body, [], oe)[@at=e@at];
}

public Script normalizeIf(Script s) {
	// NOTE: We copy the locations over. This isn't completely valid, since we are
	// then using locations for items that don't actually appear anywhere in the
	// source, but this at least helps to tie these back to the original code.
	solve(s) {
		s = bottom-up visit(s) {
			case i:\if(cond,body,elseifs,els) : {
				if (size(elseifs) > 0) {
					workingElse = els;
					for (e <- reverse(elseifs)) {
						newIf = createIf(e, workingElse);
						workingElse = someElse(\else([newIf])[@at=newIf@at])[@at=newIf@at];
					}
					insert(\if(cond,body,[],workingElse)[@at=i@at]);
				}
			}
		}
	}
	return s;
}

public Script flattenBlocks(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case list[Stmt] stmtList: [*xs,block(list[Stmt] ys),*zs] => [*xs,*ys,*zs]
		}
	}
	return s;
}

public Script discardEmpties(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case list[Stmt] stmtList: [*xs,emptyStmt(),*zs] : {
				list[Stmt] r = [*xs,*zs];
				insert(r);
			}
		}
	}
	return s;
}

public Script useBuiltins(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case call(name(name("isset")),params) => isSet([e | actualParameter(e,_,_) <- params])

			case call(name(name("exit")),[]) => exit(noExpr(), true)

			case call(name(name("exit")),[actualParameter(e,_,_)]) => exit(someExpr(e), true)

			case call(name(name("die")),[]) => exit(noExpr(), false)

			case call(name(name("die")),[actualParameter(e,_,_)]) => exit(someExpr(e), false)

			case call(name(name("print")),[actualParameter(e,_,_)]) => Expr::print(e)

			case exprstmt(call(name(name("unset")),params)) => unset([e | actualParameter(e,_,_) <- params])

			case call(name(name("empty")),[actualParameter(e,_,_)]) => empty(e)

			case call(name(name("eval")),[actualParameter(e,_,_)]) => eval(e)
		}
	}
	return s;
}

public Script discardHTML(Script s) {
	solve(s) {
		s = bottom-up visit(s) {
			case inlineHTML(_) => inlineHTML("")
		}
	}
	return s;
}


data System
	= system(map[loc fileloc, Script scr] files)
	| namedVersionedSystem(str name, str version, loc baseLoc, map[loc fileloc, Script scr] files)
	| namedSystem(str name, loc baseLoc, map[loc fileloc, Script scr] files)
	| locatedSystem(loc baseLoc, map[loc fileloc, Script scr] files)
	;

public System normalizeSystem(System s) {
	s = discardErrorScripts(s);
	for (l <- s.files) {
		s.files[l] = oldNamespaces(s.files[l]);
		s.files[l] = normalizeIf(s.files[l]);
		s.files[l] = flattenBlocks(s.files[l]);
		s.files[l] = discardEmpties(s.files[l]);
		s.files[l] = useBuiltins(s.files[l]);
		s.files[l] = discardHTML(s.files[l]);
	}
	return s;
}


public System discardErrorScripts(System s) {
	s.files = (l : s.files[l] | l <- s.files, script(_) := s.files[l]);
	return s;
}