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
	| fetchConst(Name name)
	| empty(Expr expr)
	| suppress(Expr expr)
	| eval(Expr expr)
	| exit(OptionExpr exitExpr, Bool b)
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

public data StaticVar = staticVar(str name, OptionExpr defaultValue);

public data Script = script(list[Stmt] body) | errscript(str err);

public Script useBuiltins(Script s) {
		return bottom-up visit(s) {
			case call(nameE(name(n_isset())),params) => ({
			   list[Expr] es = [];
			   for (ap <- params)
			     switch(ap) {
			       case actualParameter(e,_,_):
			         es = es + [e];
			       case _:;
			     };
			   isSet(es);
			})

			case call(nameE(name(n_exit())), params) => ({
			  OptionExpr ine;
			  switch (params) {
			    case []: ine = noExpr();
			    case [actualParameter(e, _, _), *ps]: ine = someExpr(e);
			  };
			  exit(ine, true);
			})

			case call(nameE(name(n_die())), params) => ({
			  OptionExpr ine;
			  switch (params) {
			    case []: ine = noExpr();
			    case [actualParameter(e, _, _)]: ine = someExpr(e);
			  };
			  exit(ine, false);
			})

			case call(nameE(name(n_print())), params) => ({
			     Expr ine;
			     switch (params) {
			        case [actualParameter(e,_,_)]: ine = e;
			     }
			     printE(ine);
			 })

			case exprstmt(call(nameE(name(n_unset())),params)) => ({
			   list[Expr] es = [];
			   for (ap <- params)
			     switch(ap) {
			       case actualParameter(e,_,_):
			         es = es + [e];
			       case _:;
			     };
			   unset(es);
			})

			case call(nameE(name(n_empty())), params) => ({
			    Expr ine;
                switch (params) {
                    case [actualParameter(e,_,_)]: ine = e;
                };
                empty(ine);
			})

			case call(nameE(name(n_eval())), params) => ({
			    Expr ine;
			    switch (params) {
			        case [actualParameter(e,_,_)]: ine = e;
			    };
                eval(ine);
			})
		};
}

public Script discardHTML(Script s) {
	return bottom-up visit(s) {
			case inlineHTML(_) => inlineHTML(no_html_text())
    };
}