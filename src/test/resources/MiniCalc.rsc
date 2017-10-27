module MiniCalc

/*
  Inspired by the Expr language of Programming Language Concepts
*/

data Nat = zero() | suc(Nat p);

data CExpr = csti(Nat i) | cstb(bool b) | var(str x)
           | add(CExpr lop, CExpr rop)  | sub(CExpr lop, CExpr rop) 
           | mult(CExpr lop, CExpr rop) | leq(CExpr lop, CExpr rop)
           | and(CExpr lop, CExpr rop)  | not(CExpr lop)
           | ifte(CExpr cex, CExpr tex, CExpr eex)
           | let(str x, CExpr rex, CExpr bex);
           
data CType = intt() | boolt();

data CInstr = ipushi(Nat i) | iload(Nat x)
            | iadd() | isub() | imult() | ileq()
            | iand() | inot() | iswap() | ipop() 
            | label(str name) | iifzero(str label) | igoto(str label);

data CVal = vali(Nat i) | valb(bool b);

data CRVal = bound(str x) | intermediate();

Nat addnat(Nat i1, Nat i2) {
  switch(i1) {
    case zero(): i2;
    case suc(i1n): suc(addnat(i1n, i2));  
  }
}

Nat pred(Nat i) {
  switch(i) {
    case zero(): zero();
    case suc(i1n): i1n;
  }
}

Nat subnat(Nat i1, Nat i2) {
  switch(i2) {
    case zero(): i1;
    case suc(i2n): subnat(pred(i1), i2n);
  }
}

Nat multnat(Nat i1, Nat i2) {
  switch(i1) {
    case zero(): zero();
    case suc(i1n): addnat(i2, multnat(i1n, i2));
  }
}

bool leqnat(Nat i1, Nat i2) {
  switch(i1) {
    case zero(): true;
    case suc(i1n):
      switch(i2) {
         case zero(): false;
         case suc(i2n): leqnat(i1n, i2n);
      }
  }
}

/*
Expression simplification: combined constant folding and dead code analysis
*/
CExpr simplify(CExpr e) = bottom-up visit(e) {
  case add(csti(i1), csti(i2))     => csti(addnat(i1, i2))
  case add(csti(zero()), y)        => y
  case add(x, csti(zero()))        => x
  case sub(csti(i1), csti(i2))     => csti(subnat(i1, i2))
  case sub(x, csti(zero()))        => x
  case sub(x, x)                   => csti(zero())
  case mult(csti(i1), csti(i2))    => csti(multnat(i1,i2))
  case mult(csti(zero()), y)       => csti(zero())
  case mult(x, csti(zero()))       => csti(zero())
  case mult(csti(suc(zero())), y)  => y
  case mult(x, csti(suc(zero())))  => x
  case leq(csti(i1), csti(i2))     => cstb(leqnat(i1,i2))
  case leq(csti(zero()), y)        => cstb(true)
  case and(cstb(true),  y)         => y
  case and(cstb(false), y)         => cstb(false)
  case and(x, cstb(true))          => x
  case and(x, cstb(false))         => cstb(false)
  case not(cstb(false))            => cstb(true)
  case not(cstb(true))             => cstb(false)
  case ifte(cstb(false), te, ee)   => ee
  case ifte(cstb(true), te, ee)    => te
};

data TypeError = typeError();

/*
Type inference
*/
CType inferType(CExpr e, map[str, CType] tenv) {
  switch(e) {
    case csti(i): intt();
    case cstb(b): boolt();
    case var(x): tenv[x];
    case add(lop, rop): 
      if (inferType(lop, tenv) == intt() && inferType(rop, tenv) == intt()) { intt(); }
      else { throw typeError(); }
    case sub(lop, rop):
      if (inferType(lop, tenv) == intt() && inferType(rop, tenv) == intt()) { intt(); }
      else { throw typeError(); }
    case mult(lop, rop):
      if (inferType(lop, tenv) == intt() && inferType(rop, tenv) == intt()) { intt(); }
      else { throw typeError(); }
    case leq(lop, rop):
      if (inferType(lop, tenv) == intt() && inferType(rop, tenv) == intt()) { boolt(); }
      else { throw typeError(); }
    case and(lop, rop): 
      if (inferType(lop, tenv) == boolt() && inferType(rop, tenv) == boolt()) { boolt(); }
      else { throw typeError(); }
    case not(lop): 
      if (inferType(lop, tenv) == boolt()) { boolt(); }
      else { throw typeError(); }
    case ifte(cex, tex, eex): 
      {
        CType tt = inferType(tex, tenv);
        if (inferType(cex, tenv) == boolt() && inferType(eex, tenv) == tt) { tt; }
        else { throw typeError(); }
      } 
    case let(x, rex, bex): 
      {
        CType rt = inferType(rex, tenv);
        inferType(bex, tenv + (x: rt));
      }
  }
}

CType inferTypeC(CExpr e) = inferType(e, ());

/*
 Evaluation
*/
CVal eval(CExpr e, map[str, CVal] env) {
  switch(e) {
    case csti(i): vali(i);
    case cstb(b): valb(b);
    case var(x): env[x];
    case add(lop, rop): 
      switch(eval(lop, env)) {
        case vali(i1):
          switch(eval(rop, env)) {
            case vali(i2): vali(addnat(i1,i2));
            case _: throw typeError();
          }
        case _: throw typeError();
      }
    case sub(lop, rop):
      switch(eval(lop, env)) {
        case vali(i1):
          switch(eval(rop, env)) {
            case vali(i2): vali(subnat(i1,i2));
            case _: throw typeError();
          }
        case _: throw typeError();
      }
    case mult(lop, rop):
      switch(eval(lop, env)) {
        case vali(i1):
          switch(eval(rop, env)) {
            case vali(i2): vali(multnat(i1,i2));
            case _: throw typeError();
          }
        case _: throw typeError();
      }
    case leq(lop, rop):
      switch(eval(lop, env)) {
        case vali(i1):
          switch(eval(rop, env)) {
            case vali(i2): valb(leqnat(i1,i2));
            case _: throw typeError();
          }
        case _: throw typeError();
      }
    case and(lop, rop): 
      switch(eval(lop, env)) {
        case valb(b1):
          switch(eval(rop, env)) {
            case valb(b2): valb(b1 && b2);
            case _: throw typeError();
          }
        case _: throw typeError();
      }
    case not(lop): 
      switch(eval(lop, env)) {
        case valb(b1): valb(!b1);
        case _: throw typeError();
      }
    case ifte(cex, tex, eex): 
      switch(eval(cex, env)) {
        case valb(true): eval(tex, env);
        case valb(false): eval(eex, env);
        case _: throw typeError();
      }
    case let(x, rex, bex): 
      {
        CVal rv = eval(rex, tenv);
        eval(bex, env + (x: rv));
      }
  }
}

CVal evalC(CExpr e) = eval(e, ());

/*
 Compilations
*/
data NoVar = noVar();

Nat lookupCVar(list[CRVal] cenv, CRVal v) {
  switch(cenv) {
    case []: throw noVar();
    case [v, *cenvr]: zero();
    case [_, *cenvr]: suc(lookupCVar(cenvr, v));
  }
}

int counter = 0;

str mklabel() {
  counter = counter + 1;
  "label" + "<counter>";
}

list[CInstr] compile(CExpr e, list[CRVal] cenv) {
  switch(e) {
    case csti(i): [ipushi(i)];
    case cstb(b): [ipushi(b ? 1 : 0)];
    case var(x):  [iload(lookupCVar(cenv, bound(x)))];
    case add(lop, rop): 
      compile(lop, cenv) + compile(rop, [intermediate()] + cenv) + [iadd()];
    case sub(lop, rop): 
      compile(lop, cenv) + compile(rop, [intermediate()] + cenv) + [isub()];
    case mult(lop, rop): 
      compile(lop, cenv) + compile(rop, [intermediate()] + cenv) + [imult()];
    case leq(lop, rop): 
      compile(lop, cenv) + compile(rop, [intermediate()] + cenv) + [ileq()];
    case and(lop, rop): 
      compile(lop, cenv) + compile(rop, [intermediate()] + cenv) + [iand()];
    case not(lop): 
      compile(lop, cenv) + [not()];
    case ifte(cex, tex, eex): 
      {
        str l1 = mklabel();
        str l2 = mklabel();
        compile(cex, cenv) + [ifzero(l1)] + compile(tex, cenv) + [goto(l2), label(l1)] + compile(eex, cenv) + [label(l2)];
      } 
    case let(x, rex, bex): 
      compile(rex, cenv) + compile(bex, [bound(x)] + cenv) + [iswap(), ipop()];
  }
}