package Symbolic;
import java.io.Serializable;

import Expression.Expr;
import Expression.Operator;


public class Symbolic extends Expr
{

	public Symbolic() 
	{
		super(Operator.NULL, null);
	}
	

	public boolean equals(Symbolic b)
	{
		if(this instanceof Int && b instanceof Int)
			return ((Int)this).equals((Int)b);
		if(this instanceof Rational && b instanceof Rational)
			return ((Rational)this).equals((Rational)b);
		if(this instanceof Rational && b instanceof Int)
			return ((Rational)this).equals(new Rational((Int)b, Int.ONE));
		if(this instanceof Int && b instanceof Rational)
			return ((Rational)b).equals(new Rational((Int)this, Int.ONE));
		if(this instanceof Var && b instanceof Var)
			return ((Var)this).equals((Var)b);
		if(this instanceof ModIntSym && b instanceof ModIntSym)
			return ((ModIntSym)this).equals((ModIntSym)b);
		if(this instanceof ModIntNon && b instanceof ModIntNon)
			return ((ModIntNon)this).equals((ModIntNon)b);
		if(this instanceof Str && b instanceof Str)
			return ((Str)this).equals((Str)b);
		return false;
	}
	
	@Override
	public int length()
	{
		return 0;
	}
	
}
