module MiniConfigMod

/*
 miniC90 - based on https://github.com/usethesource/rascal/blob/master/src/org/rascalmpl/library/lang/c90/syntax/C.rsc
*/

data StatementSeq = sseq(Statement init, StatementSeq rests) | sskip();

data Statement = block(StatementSeq inner)
               | expr(Expression e)
               | \if(Expression cond, Statement then)
               | ifelse(Expression cond, Statement then, Statement \else)
               | \switch(Expression scrutinee, list[Case] cases, Statement \default)
               | \while(Expression cond, Statement body)
               | doWhile(Statement body, Expression cond)
               | \for(Expression initz, Expression cond, Expression step, Statement body)
               | \continue()
               | \break()
               | \return()
               | returnE(Expression e) ;

data Case = \case(Const cst, Statement s);

data Expression = const(Const const)
                | access(Access acc)
                | call(Expression fun, list[Expression] se)
                | sizeof(Expression e)
                | preop(Preop preop, Expression e)
                | postop(Expression e, Postop postop)
                | binop(Expression e1, Binop binop, Expression e2)
                | assign(Access acc, Expression e)
                | ternary(Expression cond, Expression then, Expression \else)
                ;

data Access = var(str name)
            | arrayaccess(Expression tar, Expression indx)
            | fieldaccess(Expression e, str field)
            | ifieldaccess(Expression e, str field);

data Preop = neg() | not() | deref() | ref();
data Postop = incr() | decr();
data Binop = and() | or() | times() | plus() | minus() | div() | eq() | leq() ;

data Const = intv(int ival) | strv(str sval) | boolv(bool bval);

data Exc = precondExc() | postcondExc();

Expression modernize(Statement stmt) {
  Statement stmtsup = ensureSupported(stmt);
  Statement stmtpure = ensureAllPure(stmtsup);
  Statement stmtnoswitch = switchToIf(stmtpure);
  Statement stmtifsconverted = convertIfs(stmtnoswitch);
  Statement stmtnoemptyifs = removeEmptyIfs(stmtifsconverted);
  Statement stmtifelses = ifsToIfElses(stmtnoemptyifs);
  Statement stmtexpr = statementToExpression(stmtifelses);
  return extractExpression(stmtexpr);
}

Expression ensurePure(Expression e) = top-down visit (e) {
   case assign(_,_) => ({ throw precondExc(); })
   case postop(_,_) => ({ throw precondExc(); })
   // Assume function calls are pure
};

Statement ensureAllPure(Statement s) = top-down visit(s) {
   case \if(e,s) => \if(ensurePure(e), s)
   case ifelse(e,s1,s2) => ifelse(ensurePure(e), s1, s2)
   case \switch(e,cs,ds) => \switch(ensurePure(e), cs, ds)
};

Statement ensureSupported(Statement s) = top-down visit (s) {
  case expr(_) => ({ throw precondExc(); })
  case doWhile(_,_) => ({ throw precondExc(); })
  case \while(_,_) => ({ throw precondExc(); })
  case \for(_,_,_,_) => ({ throw precondExc(); })
  case \continue() => ({ throw precondExc(); })
  case \break() => ({ throw precondExc(); })
  case \return() => ({ throw precondExc(); })
  case block(sskip()) => ({ throw precondExc(); })
  case sseq(\if(_,_),sskip()) => ({ throw precondExc(); })
};

Statement switchToIf(Statement stmt) = bottom-up visit(stmt) {
  case \switch(scrutinee, cases, def) => {
        Statement resIf = def;
        for (c <- cases) {
           switch(c) {
             case \case(cst, s): resIf = ifelse(binop(const(cst), eq(), scrutinee), s, resIf);
           }
        };
        resIf;
    }
};

Statement convertIfs(Statement stmt) = bottom-up visit(stmt) {
   case ifelse(e, s1, s2) => ((s1 == s2) ? s1 : ifelse(e, s1, s2))
   case \if(e1, \if(e2, s)) => \if(binop(e1, and(), e2), s)
   case block(sseq(\if(e1, st), sseq(\if(e2,st), ss))) => block(sseq(\if(binop(e1, or(), e2), st), ss))
   case block(sseq(ifelse(e1, st, sf), sseq(ifelse(e2,st,sf), ss))) => block(sseq(ifelse(binop(e1, or(), e2), st, sf), ss))
   case block(sseq(\if(e1, s), sseq(sel: \if(_,_), sseq(\if(e2, s), ss)))) => block(sseq(\if(binop(e1, or(), e2), s), sseq(sel, ss)))
   case ifelse(e1, returnE(const(boolv(true))), returnE(const(boolv(false)))) => returnE(e1)
   case ifelse(e1, returnE(const(boolv(false))), returnE(const(boolv(true)))) => returnE(preop(not(),e1))
};

Statement removeEmptyIfs(Statement stmt) = bottom-up visit(stmt) {
   case block(sseq(\if(e1, block(sskip())), ss)) => block(ss)
   case block(sseq(ifelse(e1, block(sskip()), block(sskip())), ss)) => block(ss)
};

Statement ifsToIfElses(Statement stmt) = top-down visit(stmt) {
   case \if(e, s) => ifelse(e, s, block(sskip()))
   case block(sseq(\if(e, s), ss)) => block(sseq(ifelse(e, s, block(ss)), sskip()))
   case block(sseq(ifelse(e, st, sf), ss)) => block(sseq(ifelse(e, block(sseq(st, ss)), block(sseq(sf, ss))), sskip()))
};

Statement statementToExpression(Statement stmt) = bottom-up visit(stmt) {
    case ifelse(e, expr(et), expr(ef)) => expr(ternary(e, et, ef))
    case \returnE(e) => expr(e)
    case block(sseq(expr(e), sskip())) => expr(e)
};

Expression extractExpression(Statement stmt) {
  switch (stmt) {
    case expr(e): return e;
    case _: throw postcondExc();
  }
}
