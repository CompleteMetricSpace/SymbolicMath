package calculus;

import algebra.Algebra;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;

public class Calculus 
{
    private static Expr[] continuous = new Expr[]{Operator.EXP, Operator.ABSOLUTE_VALUE, Operator.SIN,
    	Operator.COS, Operator.SINH, Operator.COSH, Operator.ARCTAN};

	public static boolean is_continuous(Expr f, Expr x, Expr a)
    {
		if(f.equals(x))
			return true;
    	if(f.isFreeOf(x))
    		return true;
    	if(f.isSum())
    	{
    		return is_continuous(f.get(0), x, a) && is_continuous(f.sub(f.get(0)), x, a);
    	}
    	if(f.isProduct())
    	{
    		return is_continuous(f.get(0), x, a) && is_continuous(f.div(f.get(0)), x, a);
    	}
    	Expr[] nd = Algebra.NumeratorDenominator(f);
    	if(!nd[1].equals(Int.ONE))
    	{
    		Expr p = Simplification.simplify_recursive(nd[1].substitute(x, a));
    		if(Simplification.isZero(p))
    			return false;
    		else
    		    return is_continuous(nd[0], x, a) && is_continuous(nd[1], x, a);
    	}
    	if(f.isPower())
    	{
    		return is_continuous(f.get(0), x, a) && is_continuous(f.get(1), x, a);
    	}
    	if(Set.member(continuous , f.getOperator()))
    	{
    		return is_continuous(f.get(0), x, a);
    	}
    	return false;
    }
}
