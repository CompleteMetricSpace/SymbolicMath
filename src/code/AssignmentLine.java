package code;

import Expression.Expr;
import Symbolic.Var;

public class AssignmentLine extends Line //Assignment x := expr
{
    Var[] variable;
    Expr[] expression;
    
    public AssignmentLine(Var[] v, Expr[] e)
    {
    	variable = v;
    	expression = e;
    }
    
    public Var[] getVariable()
    {
    	return variable;
    }
    
    public Expr[] getExpression()
    {
    	return expression;
    }
    
}
