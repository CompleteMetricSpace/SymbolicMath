package calculus;

import Expression.Expr;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;

public class HeuristicSummation 
{
	public static Expr summate(Expr u, Expr k)
	{
		return null;
	}
	
	public static Expr summate_power(Expr k, Int p)
	{
	    return null;
	}
	
	public static Expr summate_linear_properties(Expr u, Expr k)
	{
		if(u.isProduct())
		{
			Expr[] cv = Simplification.constant_term(u, k);
			if(!cv[0].equals(Int.ONE))
			{
				Expr v = summate(cv[1], k);
				if(!v.equals(Constant.FAIL))
					return cv[0].mul(v);
			}
		}
		if(u.isSum())
		{
			Expr s = Int.ZERO;
			for(int i = 0;i<u.length();i++)
			{
				Expr f = summate(u.get(i), k);
				if(f.equals(Constant.FAIL))
					return Constant.FAIL;
				else
					s = s.add(f);
			}
			return s;
		}
		return Constant.FAIL;
	}
}
