package code;

import Expression.Expr;

public class ReturnLine extends Line
{
    Expr return_expr;
    
    public ReturnLine(Expr r)
    {
    	return_expr = r;
    }
    
    public Expr getReturn()
    {
    	return return_expr;
    }
    
}
