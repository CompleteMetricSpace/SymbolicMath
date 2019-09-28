package code;

import Expression.Expr;

public class WriteLine extends Line
{
    private Expr write;
    
    public WriteLine(Expr w)
    {
    	write = w;
    }
    
    public Expr getWriteExpr()
    {
    	return write;
    }
}
