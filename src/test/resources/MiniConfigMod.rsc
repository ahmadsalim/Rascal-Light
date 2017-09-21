module MiniConfigMod

/*
 miniC90 - based on https://github.com/usethesource/rascal/blob/master/src/org/rascalmpl/library/lang/c90/syntax/C.rsc
*/

data StatementSeq = sseq(Statement inits, StatementSeq rests) | sskip();

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

data Case = \case(Expression e, Statement s); 

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

data Const = intv(int val) | strv(str val) | floatv(real val) ;