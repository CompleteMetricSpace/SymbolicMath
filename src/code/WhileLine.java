package code;

import Expression.Expr;

public class WhileLine extends Line
{
    Expr condition;
    Line[] code;
    
    public WhileLine(Expr c, Line[] cd)
    {
    	condition = c;
    	code = cd;
    }
    
    public Line[] getCode()
    {
    	return code;
    }
    
    public Expr getCondition()
    {
    	return condition;
    }
}
