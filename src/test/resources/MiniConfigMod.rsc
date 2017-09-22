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
               | \returnE(Expression e) ;

data Case = \case(Const cst, Statement s); 

data Expression = const(Const const)
                | access(Access acc)                
                | call(Expression fun, list[Expression] se)
                | sizeof(Expression e)
                | preop(Preop op, Expression e)
                | postop(Expression e, Postop op)
                | binop(Expression e1, Binop op, Expression e2)
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

data Const = intv(int val) | strv(str val) | floatv(real val) | boolv(bool val);

data PrecondExc = precondExc();
data PostcondExc = postcondExc();

Expression ensurePure(Expression e) = top-down-break visit (e) {
   case assign(_,_): throw precondExc();
   case postop(_, incr()): throw precondExc();
   case postop(_, decr()): throw precondExc();
   // Assume function calls are pure
};

Statement switchToIf(Statement stmt) = bottom-up visit(stmt) {
  case \switch(scrutinee, cases, def) => {
        list[Expression] resIf = def;
        for (c <- cases) {
           switch(c) {
             case \case(cst, s): resIf = ifelse(binop(const(cst), eq(), scrutinee), s, resIf);
           }
        };
        resIf;
    }
};

Statement convertIfs(Statement stmt) = bottom-up visit(stmt) {
   case ifelse(e, s, s) => s
   case \if(e1, \if(e2, s)) => \if(binop(e1, and(), e2), s)
   case sseq(\if(e1, st), sseq(\if(e2,st), ss)) => sseq(\if(binop(e1, or(), e2), st), ss)
   case sseq(ifelse(e1, st, sf), sseq(ifelse(e2,st,sf), ss)) => sseq(ifelse(binop(e1, or(), e2), st, sf), ss)
   case sseq(\if(e1, s), sseq(sel: \if(_,_), sseq(\if(e2, s), ss))) => sseq(\if(binop(e1, or(), e2), s), sseq(sel, ss))
   case \if(e1, \return(const(boolv(true))), \return(const(boolv(false)))) => \return(e1)
   case \if(e1, \return(const(boolv(false))), \return(const(boolv(true)))) => \return(preop(not(),e1))
};

Statement removeEmptyIfs(Statement stmt) = bottom-up visit(stmt) {
   case sseq(\if(e1, block(sskip())), ss) => ss
   case sseq(ifelse(e1, block(sskip()), block(sskip())), ss) => ss  
};

Statement ifsToIfElses(Statement stmt) = bottom-up visit(stmt) {
   case sseq(\if(e, s), ss) => ifelse(e, s, block(ss))
   case sseq(ifelse(e, st, sf), ss) => ifelse(e, sseq(st, sf), sseq(sf, ss)) 
};

Statement singletonBlocksToStatements(Statement stmt) = bottom-up visit(stmt) {
   case block(sseq(s, sskip())) => s
};
 
Expression statementToExpression(Statement stmt) {
  switch (stmt) {
    case ifelse(e, st, sf): return ternary(e, statementToExpression(st), statementToExpression(sf));
    case \return(e): return e;
    case _: throw postcondExc(); 
  }
}