package code;

import Expression.Expr;
import Symbolic.Var;

public class ProgramReturn 
{
    Expr return_expr;
    Var[] varlist;
    Expr[] values;
    String end;
    
    public ProgramReturn(Expr r, Var[] vr, Expr[] vl, String n)
    {
    	return_expr = r;
    	varlist = vr;
    	values = vl;
    	end = n;
    }
    
    public Expr getReturnExpr()
    {
    	return return_expr;
    }
    
    public Var[] getVars()
    {
    	return varlist;
    }
    
    public Expr[] getValues()
    {
    	return values;
    }
    
    public String getEnd()
    {
    	return end;
    }
}
