package code;

import Expression.Expr;

public class ForLine extends Line
{
    AssignmentLine assign;
    Expr condition;
    Line iteration;
    Line[] code;
    
    public ForLine(AssignmentLine a, Expr c, Line it, Line[] cd)
    {
    	assign = a;
    	condition = c;
    	iteration = it;
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
    
    public Line getIteration()
    {
    	return iteration;
    }
    
    public AssignmentLine getAssignment()
    {
    	return assign;
    }
    
    
}
