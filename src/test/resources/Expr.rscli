module Expr

data Nat = zero() | suc(Nat pre);
data Expr = var(str nm) | cst(Nat vl) | mult(Expr el, Expr er);

Expr simplify(Expr expr) = bottom-up visit (expr) {
	case mult(cst(zero()), y) => cst(zero())
	case mult(x, cst(zero())) => cst(zero())
	case mult(cst(suc(zero())), y) => y
	case mult(x, cst(suc(zero()))) => x
};

test bool simplify_test1() = {
  Expr input = mult(mult(var("x"), cst(zero())), mult(var("y"), cst(suc(suc(suc(zero()))))));
  Expr expected = cst(zero());
  return simplify(input) == expected;
};

test bool simplify_test2() = {
  Expr input = mult(mult(var("x"), cst(suc(zero()))), mult(cst(suc(zero())), mult(var("y"), cst(suc(suc(suc(zero())))))));
  Expr expected = mult(var("x"), mult(var("y"), cst(suc(suc(suc(zero()))))));
  return simplify(input) == expected;
};

test bool simplify_test3() = {
  Expr input = mult(mult(var("x"), cst(suc(zero()))), mult(var("z"), mult(var("y"), cst(suc(suc(suc(zero())))))));
  Expr expected = mult(var("x"), mult(var("z"), mult(var("y"), cst(suc(suc(suc(zero())))))));
  return simplify(input) == expected;
};