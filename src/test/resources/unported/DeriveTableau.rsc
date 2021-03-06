module DeriveTableau

/*
 Based on https://github.com/cwi-swat/et-al/blob/master/src/et_al/Tableau.rsc
*/

data RExpr
  = union(set[RExpr] xs)
  | isect(set[RExpr] xs)
  | diff(list[RExpr] args)
  | compose(list[RExpr] args)
  | dagger(list[RExpr] args)
  | inv(RExpr arg)
  | not(RExpr arg)
  | id(str class)
  | div(str class)
  | total(str class)
  | total2(str from, str to)
  | empty()
  | implies(RExpr lhs, RExpr rhs)
  | equals(RExpr lhs, RExpr rhs)
  | base(str name, str from, str to)
;

data Signed
  = F(RExpr expr)
  | T(RExpr expr)
  ;

data Tableau
 = alt(set[Tableau] args)

 | seq(set[Tableau] args)

 // for all var, chose one of args
 | seq(Var var, set[Tableau] args)

 // for any var, do all of args
 | alt(Var var, set[Tableau] args)

 | del(Var a, Var b, RExpr arg)
 | add(Var a, Var b, RExpr arg)
 | equal(Var a, Var b)
 | nonEqual(Var a, Var b)
 ;

data Var = var(str name, str class);

Tableau derive(Signed srexpr, Var a, Var b) {
  switch (srexpr) {
  	case F(union(set[RExpr] xs)): {
  		set[Tableau] inner = {};
  		for (x <- xs)
  			inner = inner + {derive(F(x), a, b)};
  		return seq(inner);
  	}
  	case T(union(set[RExpr] xs)): {
  		set[Tableau] inner = {};
  		for (x <- xs)
  			inner = inner + {derive(T(x), a, b)};
  		return alt(inner);
  	}
  	case F(isect(set[RExpr] xs)): {
  		set[Tableau] inner = {};
  		for (x <- xs)
  			inner = inner + {derive(F(x), a, b)};
  		return alt(inner);
  	}
  	case T(isect(set[RExpr] xs)): {
  		set[Tableau] inner = {};
  		for (x <- xs)
  			inner = inner + {derive(T(x), a, b)};
  		return seq(inner);
  	}
  	case F(diff([x0, *xs])): {
  		set[Tableau] inner = {derive(F(x0), a, b)};
  		for (x <- xs)
  			inner = inner + {derive(T(x), a, b)};
  		return alt(inner);
  	}
  	case T(diff([x0, *xs])): {
  		set[Tableau] inner = {derive(T(x0), a, b)};
  		for (x <- xs)
  			inner = inner + {derive(F(x), a, b)};
  		return seq(inner);
  	}
  	case T(not(RExpr x)):
  		return derive(F(x), a, b);
  	case F(not(RExpr x)):
  		return derive(T(x), a, b);
  	case F(inv(RExpr x)):
  		return derive(F(x), b, a);
  	case T(inv(RExpr x)):
  		return  derive(T(x), b, a);
  	case T(r:base(_, _, _)):
  		return add(a, b, r);
  	case F(r:base(_, _, _)):
  		return del(a, b, r);
  	case T(empty()):
  		return alt({});
  	case F(empty()):
  		return seq({});
  	case T(total(str class)):
  		return derive(T(total2(class, class)), a, b);
  	case F(total(str class)):
  		return derive(F(total2(class, class)), a, b);
  	case T(total2(str f, str t)):
  		if (a.class == f && b.class == t) {
  			return seq({});
  		} else {
  			return alt({});
  		}
  	case F(total2(str f, str t)):
  	    if (a.class != f || b.class != t) {
  	    	return seq({});
  	    } else {
  	    	return alt({});
  	    }
  	case T(i:id(_)):
  		return add(a, b, i);
  	case F(i:id(_)):
  		return del(a, b, i);
  	case T(compose([x, y])): {
  	    // Assumes ran(x) == dom(x)
  		Var c = newVar(ran(x));
  		return alt(c, {derive(T(x), a, c), derive(T(y), c, b)});
  	}
  	case F(compose([x, y])): {
  		//  Assumes ran(x) == dom(x)
  		Var c = newVar(ran(x));
  		return seq(c, {derive(F(x), a, c), derive(F(y), c, b)});
  	}
  	case T(compose([x, y, z, *xs])):
  		return derive(T(compose([x, compose([y, z] + xs)])), a, b);
  	case F(compose([x, y, z, *xs])):
  		return derive(F(compose([x, compose([y, z] + xs)])), a, b);
  	case T(implies(x, y)):
  		return derive(T(union({not(x), y})), a, b);
  	case F(implies(x, y)):
  		return derive(F(union({not(x), y})), a, b);
  	case T(equals(x, y)):
  		return derive(T(isect({implies(x, y), implies(y, x)})), a, b);
  	case F(equals(x, y)):
  		return derive(F(isect({implies(x, y), implies(y, x)})), a, b);
  };
}

private int varId = -1;

Var newVar(str class) {
  varId = varId + 1;
  return var("x_" + "<varId>", class);
}

str ran(RExpr rexpr) {
	switch(rexpr) {
		case union({x, *_}): return ran(x);
		case isect({x, *_}): return ran(x);
		case diff([x, *_]): return ran(x);
		case compose([*_, x]): return ran(x);
		case inv(x): return dom(x);
		case not(x): return ran(x);
		case id(c): return c;
		case total(c): return c;
		case total2(c1, c2): return c2;
		case base(_, _, c): return c;
		// Missing empty cases, perhaps fix? Original code suggested some kind of lub
	};
}

str dom(RExpr rexpr) {
	switch (rexpr) {
		case union({x, *_}): return dom(x);
		case isect({x, *_}): return dom(x);
		case diff([x, *_]): return dom(x);
		case compose([x, *_]): return dom(x);
		case inv(x): return ran(x);
		case not(x): return dom(x);
		case id(c): return c;
		case total(c): return c;
		case total2(c1, c2): return c1;
		case base(_, c, _): return c;
		// Missing empty cases, perhaps fix? Original code suggested some kind of lub
	};
}