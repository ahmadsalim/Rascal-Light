module ConstantElimOberon

/*
*   Based on https://github.com/cwi-swat/oberon0/blob/7bed47c2098c7335a6b47c3bed1329795211b53f/src/lang/oberon0/l1/optimize/ConstantElimination.rsc
*/

data Module = 
	\mod(Ident name, Declarations decls, list[Statement] body, Ident endName)
	;

data Declarations 
	= decls(list[ConstDecl] consts, list[TypeDecl] types, list[VarDecl] vars)
	;

data ConstDecl 
	= constDecl(Ident name, Expression \value)
	;
	
data TypeDecl 
	= typeDecl(Ident name, Type \type)
	;
	
data VarDecl 
	= varDecl(list[Ident] names, Type \type)
	;

data Type 
	= user(Ident name)
	;
	
data Statement 
	= assign(Ident var, Expression exp)
	| ifThen(Expression condition, list[Statement] body, list[ElseIf] elseIfs, list[Statement] elsePart)
	| whileDo(Expression condition, list[Statement] body)
	| skip()
	;

data Expression 
	= nat(int val)
	| \true()
	| \false()
	| lookup(Ident var)
	| neg(Expression exp)
	| pos(Expression exp)
	| not(Expression exp)
	| mul(Expression lhs, Expression rhs)
	| div(Expression lhs, Expression rhs)
	| \mod(Expression lhs, Expression rhs)
	| amp(Expression lhs, Expression rhs)
	| add(Expression lhs, Expression rhs)
	| sub(Expression lhs, Expression rhs)
	| or(Expression lhs, Expression rhs)
	| eq(Expression lhs, Expression rhs)
	| neq(Expression lhs, Expression rhs)
	| lt(Expression lhs, Expression rhs)
	| gt(Expression lhs, Expression rhs)
	| leq(Expression lhs, Expression rhs)
	| geq(Expression lhs, Expression rhs)
	;

data Ident 
	= id(str name)
;


data Case
	= guard(Expression guard, list[Statement] body)
;

data ElseIf = elseif(Expression condition, list[Statement] body);


public Module eliminateConstants(Module m) {
	constantMap = getConstants(m.decls.consts,());
	m.decls.consts = [];
	m.body = top-down-break visit(m.body){
		case Expression e => evaluate(constantMap,e)
    };
    return m;
}

map[Ident,int] getConstants(list[ConstDecl] constants, map[Ident,int] constantMap){
	for(cst <- constants){
		switch(cst) {
			case constDecl(name,exp):
				switch(evaluate(constantMap,exp)) {
					case nat(i):
						constantMap[name]=i;
				}
		}
 	}
	return constantMap;
}

Expression evaluate(map[Ident,int] constants, Expression exp){
	return innermost visit(exp){
		case e : lookup(var)      =>
			(var in constants) ? nat(constants[var]) : e 
		case amp(_, \false()) 		=> \false()
		case amp(\false(), _) 		=> \false()
		case amp(\true(), \true()) 	=> \true()

		case or(_, \true()) 		=> \true()
		case or(\true(), _) 		=> \true()
		case or(\false(), \false()) => \false()
		
		case not(\false())			=> \true()
		case not(\true())			=> \false()
		
		
		case neg(nat(val))          => nat(- val)
		case pos(nat(val))          => nat(val)
		case mul(lhs,nat(0))        => nat(0)
		case mul(nat(0),rhs)        => nat(0)
		case mul(nat(1),rhs)        => rhs
		case mul(lhs,nat(1))        => lhs
		case add(lhs,nat(0))        => lhs
		case add(nat(0),rhs)        => rhs
		case div(lhs,nat(1))        => lhs
		case sub(lhs,nat(0))        => lhs
		case sub(nat(0),rhs)        => neg(rhs)
		case mul(nat(lhs),nat(rhs)) => nat(lhs * rhs)
		case div(nat(lhs),nat(rhs)) => nat(lhs / rhs)
		case \mod(nat(lhs),nat(rhs)) => nat(lhs % rhs)
		case add(nat(lhs),nat(rhs)) => nat(lhs + rhs)
		case sub(nat(lhs),nat(rhs)) => nat(lhs - rhs)
		
		// no side effects in exps, so must be true
		case eq(x,x)  				=> \true()
		
		case neq(nat(lhs),nat(rhs)) => lhs != rhs ? \true() : \false()
		case lt(nat(lhs),nat(rhs)) => lhs < rhs ? \true() : \false()
		case gt(nat(lhs),nat(rhs)) => lhs > rhs ? \true() : \false()
		case leq(nat(lhs),nat(rhs)) => lhs <= rhs ? \true() : \false()
		case geq(nat(lhs),nat(rhs)) => lhs >= rhs ? \true() : \false()

		// some rewrite rules for cases with unkown variables, like (x + 2) + 3
		case add(add(lhs,nat(v1)),nat(v2)) => add(lhs,nat(v1+v2))
		case add(add(nat(v1),lhs),nat(v2)) => add(lhs,nat(v1+v2))
		case add(nat(v2),add(lhs,nat(v1))) => add(nat(v1+v2),lhs)
		case add(nat(v2),add(nat(v1),lhs)) => add(nat(v1+v2),lhs)
		case mul(mul(lhs,nat(v1)),nat(v2)) => mul(lhs,nat(v1+v2))
		case mul(mul(nat(v1),lhs),nat(v2)) => mul(lhs,nat(v1+v2))
		case mul(nat(v2),mul(lhs,nat(v1))) => mul(nat(v1+v2),lhs)
		case mul(nat(v2),mul(nat(v1),lhs)) => mul(nat(v1+v2),lhs)
		case sub(sub(lhs,nat(v1)),nat(v2)) => sub(lhs,nat(v1+v2))
		case sub(sub(nat(v1),lhs),nat(v2)) => sub(nat(v1-v2),lhs)
		case sub(nat(v2),sub(lhs,nat(v1))) => sub(nat(v1+v2),lhs)
		case sub(nat(v2),sub(nat(v1),lhs)) => add(nat(v1-v2),lhs)
		case div(div(lhs,nat(v1)),nat(v2)) => div(lhs,nat(v1*v2))
		case div(div(nat(v1),lhs),nat(v2)) => div(nat(v1/v2),lhs)
		case div(nat(v1),div(lhs,nat(v2))) => div(nat(v1*v2),lhs)
		case div(nat(v1),div(nat(v2),rhs)) => mul(nat(v1/v2),rhs)
	}
}