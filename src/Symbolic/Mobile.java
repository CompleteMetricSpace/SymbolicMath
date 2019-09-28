package Symbolic;

import Expression.Expr;

public class Mobile extends Var
{

	Expr wild;
	public Mobile(String name, Expr w) 
	{
		super(name);
		wild = w;
	}
	
	public Expr getExpression()
	{
		return wild;
	}

}
