package calculus;

import algebra.Algebra;
import algebra.MatchForm;
import Expression.Expr;
import Expression.Operator;
import Expression.RecursionLimitReachedException;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;

public class LaplaceTransform 
{

	public static int RECURSIVE_LAPLACE_TRANSFORM = 50;
	public static int IT = 0;
	
	/**
	 * Laplace Transformation of a function 
	 * @param f - a function of t
	 * @param t - a variable
	 * @param s - a variable
	 * @return F(s)
	 */
	public static Expr laplace_transform(Expr f, Expr t, Expr s) throws RecursionLimitReachedException
	{
		IT = 0;
		return laplace_transform_recursive(f, t, s);
	}
	
	public static Expr laplace_transform_recursive(Expr f, Expr t, Expr s) throws RecursionLimitReachedException
	{
		Expr ans = laplace_table(f, t, s);
		if(!ans.equals(Constant.FAIL))
			return ans;
		ans = laplace_linear_properties(f, t, s);
		if(!ans.equals(Constant.FAIL))
			return ans;
		ans = laplace_shift(f, t, s);
		if(!ans.equals(Constant.FAIL))
			return ans;
		ans = laplace_similarity(f, t, s);
		if(!ans.equals(Constant.FAIL))
			return ans;
		return Constant.FAIL;
	}
	
	

	private static Expr laplace_linear_properties(Expr f, Expr t, Expr s) throws RecursionLimitReachedException
	{
		if(f.isProduct())
		{
			Expr[] cv = Simplification.constant_term(f, t);
			if(!cv[0].equals(Int.ONE))
			{
				Expr v = laplace_transform_recursive(cv[1], t, s);
				if(!v.equals(Constant.FAIL))
					return cv[0].mul(v);
			}
		}
		if(f.isSum())
		{
			Expr k = Int.ZERO;
			for(int i = 0;i<f.length();i++)
			{
				Expr l = laplace_transform_recursive(f.get(i), t, s);
				if(l.equals(Constant.FAIL))
					return Constant.FAIL;
				else
					k = k.add(l);
			}
			return k;
		}
		return Constant.FAIL;
	}
	
	private static Expr laplace_table(Expr f, Expr t, Expr s) throws RecursionLimitReachedException
	{
		if(f.isFreeOf(t))
			return f.div(s);
		if(f.equals(t))
			return Int.ONE.div(s.pow(Int.TWO));
		if(f.isPower())
		{
			Expr b = f.get(0);
			Expr e = f.get(1);
			if(e.isInt() && b.equals(t))
			{
				Int n = (Int)e;
				if(n.isPositive())
					return n.factorial().div(s.pow(n.add(Int.ONE)));
			}
		}
		if(f.getOperator().equals(Operator.EXP))
		{
			if(f.get(0).equals(t))
				return Int.ONE.div(s.sub(Int.ONE));
		}
		if(f.getOperator().equals(Operator.SIN))
		{
			if(f.get(0).equals(t))
				return Int.ONE.div(s.pow(Int.TWO).add(Int.ONE));
		}
		if(f.getOperator().equals(Operator.COS))
		{
			if(f.get(0).equals(t))
				return s.div(s.pow(Int.TWO).add(Int.ONE));
		}
		if(f.getOperator().equals(Operator.SINH))
		{
			if(f.get(0).equals(t))
				return Int.ONE.div(s.pow(Int.TWO).sub(Int.ONE));
		}
		if(f.getOperator().equals(Operator.COSH))
		{
			if(f.get(0).equals(t))
				return s.div(s.pow(Int.TWO).sub(Int.ONE));
		}
		return Constant.FAIL;
	}
	
	private static Expr laplace_shift(Expr f, Expr t, Expr s) throws RecursionLimitReachedException 
	{
		Expr[] shift = get_shift(f, t);
		Expr v = Simplification.getNewVariables(1, f, t, s)[0];
		for(int i = 0;i<shift.length;i++)
		{
			Expr A = Simplification.simplify_recursive(f.substitute(t.add(shift[i]), v));
			Expr lt = laplace_transform_recursive(A, v, s);
			if(!lt.equals(Constant.FAIL))
				return Algebra.cancel(lt.mul(new Expr(Operator.EXP, Int.NONE.mul(shift[i]).mul(t))));
			else
				continue;
		}
		return Constant.FAIL;
	}

	private static Expr[] get_shift(Expr f, Expr t)
	{
		if(f.isSymbolic())
			return new Expr[]{};
		Expr[] s = new Expr[]{};
		for(int i = 0;i<f.length();i++)
			s = Set.union(s, get_shift(f.get(i), t));
		if(f.length() == 1)
		{
			Expr[] D = MatchForm.linear_form(f.get(0), t);
		    if(D != null && !D[1].equals(Int.ZERO) && D[0].equals(Int.ONE))
			    return Set.union(s, new Expr[]{D[1]});
		}
		return s;
	}
	
	private static Expr laplace_similarity(Expr f, Expr t, Expr s) throws RecursionLimitReachedException
	{
		Expr[] sim = get_similar(f, t);
		Expr v = Simplification.getNewVariables(1, f, t, s)[0];
		for(int i = 0;i<sim.length;i++)
		{
			Expr A = Simplification.simplify_recursive(f.substitute(t.mul(sim[i]), v));
			Expr lt = laplace_transform_recursive(A, v, s);
			if(!lt.equals(Constant.FAIL))
				return Algebra.cancel(lt.substitute(s, s.div(sim[i])).div(sim[i]));
			else
				continue;
		}
		return Constant.FAIL;
	}

	private static Expr[] get_similar(Expr f, Expr t) 
	{
		if(f.isSymbolic())
			return new Expr[]{};
		Expr[] s = new Expr[]{};
		for(int i = 0;i<f.length();i++)
			s = Set.union(s, get_similar(f.get(i), t));
		if(f.length() == 1)
		{
			Expr[] D = MatchForm.linear_form(f.get(0), t);
		    if(D != null && !D[0].equals(Int.ONE) && D[1].equals(Int.ZERO))
			    return Set.union(s, new Expr[]{D[0]});
		}
		return s;
	}
}
