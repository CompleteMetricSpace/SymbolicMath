package algebra;

import numerical.Evaluation;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Decimal;
import Symbolic.Int;
import Symbolic.Rational;

public class Denest 
{

	public static Int nesting_degree(Expr u)
	{
		if(u.isNumerical())
			return Int.ONE;
		if(u.isPower())
		{
			Expr b = u.get(0);
			Expr e = u.get(1);
			if(e.isRational())
				return Int.ONE.add(nesting_degree(b));
		}
		if(u.isProduct())
		{
			Int s = Int.ZERO;
			for(int i = 0;i<u.length();i++)
			{
				Int n = nesting_degree(u.get(i));
				s = s.compareTo(n)<0?n:s;
			}
			return s;
		}
		if(u.isSum())
		{
			Int s = Int.ZERO;
			for(int i = 0;i<u.length();i++)
			{
				Int n = nesting_degree(u.get(i));
				s = s.add(n);
			}
			return s;
		}
		return Int.ZERO;
	}
	
	public static Expr simplify_nested_sqrt_op(Expr E)
	{
		if(E.isNumerical())
			return E;
	    if(E.isSum()  || E.isProduct())
	    {
	    	Expr[] op = new Expr[E.length()];
	    	for(int i = 0;i<E.length();i++)
	    	{
	    		op[i] = simplify_nested_sqrt_op(E.get(i));
	    		if(op[i].equals(Constant.FAIL))
	    			op[i] = E.get(i);
	    	}
	    	return Simplification.simplify_recursive(new Expr(E.getOperator(), op));
	    }
	    if(E.isSqrt())
	    {
	    	Expr c = simplify_nested_sqrt(E);
	    	if(c.equals(Constant.FAIL))
	    		return E;
	    	return c;
	    }
	    return E;
	}
	
	public static Expr simplify_nested_sqrt(Expr E)
	{
		Int n = nesting_degree(E);
		Expr f = E.get(0);
		if(!f.isSum())
			return E;
		Expr X = f.get(0);
		Expr Y = Simplification.simplify_recursive(new Expr(Operator.ADD, Set.rest(f.getOperands())));
		Expr T = Algebra.expand(X.pow(Int.TWO).sub(Y.pow(Int.TWO)));
		if(nesting_degree(T).compareTo(n) >= 0)
			return Constant.FAIL;
		Expr F = T.pow(Rational.HALF);
		if(nesting_degree(F).compareTo(n) >= 0)
			return Constant.FAIL;
		Expr P = simplify_nested_sqrt_op(X.add(F));
		if(P.equals(Constant.FAIL))
			return Constant.FAIL;
		if(nesting_degree(P).compareTo(n) >= 0)
			return Constant.FAIL;
		Expr Q = simplify_nested_sqrt_op(X.sub(T.pow(Rational.HALF)));
		if(Q.equals(Constant.FAIL))
			return Constant.FAIL;
		if(nesting_degree(Q).compareTo(n.sub(Int.ONE)) >= 0)
			return Constant.FAIL;
		Expr NY = Evaluation.eval(Y, Decimal.DEFAULT_PRECISION);
		Int sign = null;
		if(Simplification.is_positive(NY))
			sign = Int.ONE;
		else
		{
			if(Simplification.is_negative(NY))
			    sign = Int.NONE;
			else
				return Constant.FAIL;
		}
		return P.div(Int.TWO).pow(Rational.HALF).add(sign.mul(Q.div(Int.TWO).pow(Rational.HALF)));
	}
}
