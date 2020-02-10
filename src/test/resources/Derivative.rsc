// tag::module[]
module demo::common::Derivative

data VarNominal = x() | y();

data Exp = con(int n) // <1>
         | var(VarNominal name)
         | mul(Exp e1, Exp e2)
         | add(Exp e1, Exp e2)
         ;
         
Exp dd(Exp e, VarNominal v) {
  switch (e) {
    case con(n): return con(0);
    case var(v2): return con((v2 == v) ? 1 : 0);
    case add(e1, e2): return add(dd(e1, v), dd(e2, v));
    case mul(e1, e2): return add(mul(dd(e1, v), e2), mul(e1, dd(e2, v)));
  };
}

Exp simplify(Exp e) {
  return bottom-up visit(e) {
    case add(con(n), con(m)) => con(n + m)
    case mul(con(n), con(m)) => con(n * m)
    case mul(con(1), e) => e
    case mul(e, con(1)) => e
    case mul(con(0), e) => con(0)
    case mul(e, con(0)) => con(0)
    case add(con(0), e) => e
    case add(e, con(0)) => e
  };
}

Exp derivative(Exp e, VarNominal v) {
  Exp dexp = dd(e, v);
  return simplify(dexp);
}
