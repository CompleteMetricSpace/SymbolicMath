package calculus;

import algebra.Algebra;
import polynomial.Poly;
import Expression.Expr;
import Expression.Operator;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;

public class HeuristicLimit 
{
    public static Expr limit(Expr f, Expr x, Expr a, int dir)
    {
    	return limit_rec(f, x, a, dir, 6);
    }

	private static Expr limit_rec(Expr f, Expr x, Expr a, int dir, int l) 
	{
	    if(f.isFreeOf(x))
	    	return f;
	    if(a.isFinite())
	    {
	    	if(Calculus.is_continuous(f, x, a))
	    	    return Simplification.simplify_recursive(f.substitute(x, a));
	    }
	    if(!a.isFinite())
	    {
	    	boolean pinf = a.equals(Constant.POS_INF);
	    	if(Poly.is_poly(f, x))
	    	{
	    		Int n = Poly.degree(f, x);
	    		Expr c = Poly.leading_coef(f, x);
	    		int sign = 0;
	    		if(Simplification.is_positive(c))
	    			sign = 1;
	    		if(Simplification.is_negative(c))
	    			sign = -1;
	    		if(sign != 0)
	    		{
	    			if(pinf)
	    			{
	    				if(sign > 0)
	    					return Constant.POS_INF;
	    				else
	    					return Constant.NEG_INF;
	    			}
	    			else
	    			{
	    				if(n.isOdd())
	    				{
	    					if(sign > 0)
		    					return Constant.NEG_INF;
		    				else
		    					return Constant.POS_INF;
	    				}
	    				else
	    				{
	    					if(sign > 0)
		    					return Constant.POS_INF;
		    				else
		    					return Constant.NEG_INF;
	    				}
	    			}
	    		}
	    	}
	    }
	    if(f.isSum())
	    {
	    	Expr A = limit_rec(f.get(0), x, a, dir, l);
	    	Expr B = limit_rec(f.sub(f.get(0)), x, a, dir, l);
	    	if(!A.equals(Constant.FAIL) && !B.equals(Constant.FAIL))
	    	{
	    		if(A.isFinite() && B.isFinite())
	    			return A.add(B);
	    		if(A.equals(Constant.POS_INF) && (B.isFinite() || B.equals(Constant.POS_INF)))
	    			return Constant.POS_INF;
	    		if(A.equals(Constant.NEG_INF) && (B.isFinite() || B.equals(Constant.NEG_INF)))
	    			return Constant.POS_INF;
	    		if(B.equals(Constant.POS_INF) && (A.isFinite() || A.equals(Constant.POS_INF)))
	    			return Constant.POS_INF;
	    		if(B.equals(Constant.NEG_INF) && (A.isFinite() || A.equals(Constant.NEG_INF)))
	    			return Constant.POS_INF;
	    	}
	    }
	    if(f.isProduct())
	    {
	    	Expr A = limit_rec(f.get(0), x, a, dir, l);
	    	Expr B = limit_rec(f.div(f.get(0)), x, a, dir, l);
	    	if(!A.equals(Constant.FAIL) && !B.equals(Constant.FAIL))
	    	{
	    		if(A.isFinite() && B.isFinite())
	    			return A.mul(B);
	    		if(A.equals(Constant.POS_INF) && B.equals(Constant.POS_INF))
	    			return Constant.POS_INF;
	    		if(A.equals(Constant.NEG_INF) && B.equals(Constant.NEG_INF))
	    			return Constant.POS_INF;
	    		if(A.equals(Constant.POS_INF) && Simplification.is_positive(B))
	    			return Constant.POS_INF;
	    		if(A.equals(Constant.POS_INF) && Simplification.is_negative(B))
	    			return Constant.NEG_INF;
	    		if(B.equals(Constant.POS_INF) && Simplification.is_positive(A))
	    			return Constant.POS_INF;
	    		if(B.equals(Constant.POS_INF) && Simplification.is_negative(A))
	    			return Constant.NEG_INF;
	    		if(A.equals(Constant.NEG_INF) && Simplification.is_positive(B))
	    			return Constant.NEG_INF;
	    		if(A.equals(Constant.NEG_INF) && Simplification.is_negative(B))
	    			return Constant.POS_INF;
	    		if(B.equals(Constant.NEG_INF) && Simplification.is_positive(A))
	    			return Constant.NEG_INF;
	    		if(B.equals(Constant.NEG_INF) && Simplification.is_negative(A))
	    			return Constant.POS_INF;
	    	}
	    }
	    if(f.isPower())
	    {
	    	Expr b = f.get(0);
	    	Expr e = f.get(1);
	    	Expr A = limit_rec(b, x, a, dir, l);
	    	Expr B = limit_rec(e, x, a, dir, l);
	    	if(!A.equals(Constant.FAIL) && !B.equals(Constant.FAIL))
	    	{
	    		if(A.isFinite() && B.isFinite() && !(A.equals(Int.ZERO) && B.equals(Int.ZERO)) && !(A.equals(Int.ZERO) && Simplification.is_negative(B)))
	    			return A.pow(B);
	    		if(A.equals(Constant.POS_INF) && B.equals(Constant.POS_INF))
	    			return Constant.POS_INF;
	    		if(A.equals(Constant.POS_INF) && B.isFinite() && Simplification.is_positive(B))
	    			return Constant.POS_INF;
	    		if(A.equals(Constant.POS_INF) && B.isFinite() && Simplification.is_negative(B))
	    			return Int.ZERO;
	    		if(A.equals(Constant.POS_INF) && B.equals(Constant.NEG_INF))
	    			return Int.ZERO;
	    		if(A.isFinite() && Simplification.is_positive(A.sub(Int.ONE)))
	    		{
	    			if(B.equals(Constant.POS_INF))
	    				return Constant.POS_INF;
	    			if(B.equals(Constant.NEG_INF))
	    				return Int.ZERO;
	    		}
	    		if(A.isFinite() && Simplification.is_negative(A.sub(Int.ONE)) && Simplification.is_positive(A))
	    		{
	    			if(B.equals(Constant.POS_INF))
	    				return Int.ZERO;
	    			if(B.equals(Constant.NEG_INF))
	    				return Constant.POS_INF;
	    		}
	    	}
	    }
	    if(f.getOperator().equals(Operator.EXP))
	    {
	    	Expr A = limit_rec(f.get(0), x, a, dir, l);
	    	if(!A.equals(Constant.FAIL))
	    	{
	    		if(A.isFinite())
	    			return new Expr(Operator.EXP, A);
	    		if(A.equals(Constant.POS_INF))
	    			return Constant.POS_INF;
	    		if(A.equals(Constant.NEG_INF))
	    			return Int.ZERO;
	    	}
	    }
	    if(f.getOperator().equals(Operator.LOG))
	    {
	    	Expr A = limit_rec(f.get(0), x, a, dir, l);
	    	if(!A.equals(Constant.FAIL))
	    	{
	    		if(A.isFinite() && Simplification.is_positive(A))
	    			return new Expr(Operator.LOG, A);
	    		if(A.equals(Constant.POS_INF))
	    			return Constant.POS_INF;
	    		if(A.equals(Int.ZERO))
	    			return Constant.NEG_INF;
	    	}
	    }
	    if(l > 0)
	    {
	    	Expr[] nd = Algebra.NumeratorDenominator(f);
	    	Expr A = limit_rec(nd[0], x, a, dir, l-1);
	    	Expr B = limit_rec(nd[1], x, a, dir, l-1);
	    	if((A.equals(Int.ZERO) && B.equals(Int.ZERO)) || (!A.isFinite() && !B.isFinite()))
	    	{
	    		A = Diff.derivative(nd[0], x);
	    		B = Diff.derivative(nd[1], x);
	    		return limit_rec(A.div(B), x, a, dir, l-1);
	    	}
	    }
	    return Constant.FAIL;
	}
}
