package code;

import Expression.Expr;

public class ConditionalLine extends Line
{
    Expr condition;
    Line[] con_true;
    Line[] con_false;
    
    public ConditionalLine(Expr c, Line[] t, Line[] f)
    {
    	condition = c;
    	con_true = t;
    	con_false = f;
    }
    
    public ConditionalLine(Expr c, Line[] t)
    {
    	condition = c;
    	con_true = t;
    	con_false = new Line[]{};
    }
    
    public Expr getCondition()
    {
    	return condition;
    }
    
    public Line[] getTrueCode()
    {
    	return con_true;
    }
    
    public Line[] getFalseCode()
    {
    	return con_false;
    }
}
