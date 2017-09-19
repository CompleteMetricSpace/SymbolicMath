package polynomial;

import java.util.Vector;

import algebra.Algebra;
import numerical.Evaluation;
import calculus.Diff;
import Expression.Expr;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Decimal;
import Symbolic.Int;
import Symbolic.Numerical;
import Symbolic.Symbolic;

public class Roots
{
    public static Expr[] sturm_sequence(Expr p, Expr x)
    {
    	Vector<Expr> s = new Vector<Expr>();
    	s.add(p);
    	s.add(Diff.derivative(p, x));
    	Expr r = Int.NONE.mul(BasicPoly.polynomial_remainder(s.get(0), s.get(1), x));
    	while(!r.equals(Int.ZERO))
    	{
    		s.add(r);
    		r = Int.NONE.mul(BasicPoly.polynomial_remainder(s.get(s.size()-2), s.lastElement(), x));
    	}
    	return s.toArray(new Expr[s.size()]);
    }
    
    public static Numerical max_root_bound(Expr p, Expr x)
    {
    	Numerical max = Int.ZERO;
    	Int n = Poly.degree(p, x);
    	Expr lc = Poly.coefficient_poly(p, x, n);
    	for(Int i = Int.ZERO;i.compareTo(n)<0;i = i.add(Int.ONE))
    	{
    		Expr d = Evaluation.eval(Poly.coefficient_poly(p, x, i).div(lc).abs().pow(Int.ONE.div(n.sub(i))), Decimal.DEFAULT_PRECISION);
            if(!d.isNumerical())
    			throw new IllegalArgumentException(d+" is not a numerical quantity");
    		Numerical e = (Numerical)d;
    		e = e.toExactNumerical();
    		max = max.compareTo(e)>0?max:e;
    	}
    	return Int.TWO.mul(max);
    }
    
    public static Numerical min_root_bound(Expr p, Expr x)
    {
    	Int n = Poly.degree(p, x);
    	Expr c = Algebra.expand(p.substitute(x, Int.ONE.div(x)).mul(x.pow(n)));
    	return Int.ONE.div(max_root_bound(c, x));
    }
    
    public static Int variation(Expr[] p, Expr x, Expr c)
    {
    	Int count = Int.ZERO;
    	Int old = sign(p[0], x, c);
    	for(int i = 1;i<p.length;i++)
    	{
    		Int sign = sign(p[i], x, c);
    		if(sign.equals(Int.ZERO))
    			continue;
    		if(!sign.equals(old))
    		{
    			count = count.add(Int.ONE);
    			old = sign;
    		}
    	}
    	return count;
    }
    
    public static Int sign(Expr p, Expr x, Expr c)
    {
    	if(p.equals(Int.ZERO))
    		return Int.ZERO;
    	if(c.equals(Constant.POS_INF))
    	{
    		Int n = Poly.degree(p, x);
    		Expr lc = Poly.coefficient_poly(p, x, n);
    		if(Simplification.is_positive(lc))
    			return Int.ONE;
    		if(Simplification.is_negative(lc))
    			return Int.NONE;
    		throw new IllegalArgumentException("Cannot determine sign of "+lc); //Can't decide
    	}
    	if(c.equals(Constant.NEG_INF))
    	{
    		Int n = Poly.degree(p, x);
    		Expr lc = Poly.coefficient_poly(p, x, n);
    		if(Simplification.is_positive(lc))
    		{
    			if(n.isOdd())
    				return Int.NONE;
    			else
    				return Int.ONE;
    		}
    		if(Simplification.is_negative(lc))
    		{
    			if(n.isOdd())
    				return Int.ONE;
    			else
    				return Int.NONE;
    		}
    		throw new IllegalArgumentException("Cannot determine sign of "+lc); //Can't decide
    	}
    	Expr e = Simplification.simplify_recursive(Poly.horner_evaluate(p, x, c));
    	if(e.equals(Int.ZERO))
    		return Int.ZERO;
    	if(Simplification.is_positive(e))
			return Int.ONE;
		if(Simplification.is_negative(e))
			return Int.NONE;
		throw new IllegalArgumentException("Cannot determine sign of "+e);
    }
    
    public static Numerical[][] isolate_roots(Expr p, Expr x)
    {
    	Expr[] S = sturm_sequence(p, x);
    	Int vn = variation(S, x, Constant.NEG_INF);
    	Int vp = variation(S, x, Constant.POS_INF);
    	Int N = vn.sub(vp);
    	if(N.equals(Int.ZERO))
    		return new Numerical[][]{};
    	Numerical M = max_root_bound(p, x);
    	if(N.equals(Int.ONE))
    		return new Numerical[][]{{M.mul(Int.NONE), M}};
    	Numerical[][] result = new Numerical[][]{};
    	Numerical[][] work = new Numerical[][]{{M.mul(Int.NONE), M, vn, vp}};
    	while(work.length != 0)
    	{
    		Numerical[] s = work[0];
    		work = Set.rest(work);
    		Numerical a = s[0], b = s[1];
    		Int V_a = (Int) s[2], V_b = (Int) s[3];
    		Numerical c = a.add(b).div(Int.TWO);
    		if(Poly.horner_evaluate(p, x, c).equals(Int.ZERO))
    		{
    			result = Set.add(result, new Numerical[][]{{c, c}});
    			Expr m = Algebra.expand(Poly.horner_evaluate(p, x, x.sub(c)).div(x));
    			M = min_root_bound(m, x);
    			Int V_cp = variation(S, x, c.add(M));
    			Int V_cm = V_cp.add(Int.ONE);
    			if(V_a.equals(V_cm.add(Int.ONE)))
    				result = Set.add(result, new Numerical[][]{{a, c.sub(M)}});
    			if(V_a.compareTo(V_cm.add(Int.ONE)) > 0)
    				work = Set.add(work, new Numerical[][]{{a, c.sub(M), V_a, V_cm}});
    			if(V_b.equals(V_cp.sub(Int.ONE)))
    				result = Set.add(result, new Numerical[][]{{c.add(M), b}});
    			if(V_b.compareTo(V_cm.sub(Int.ONE)) < 0)
    				work = Set.add(work, new Numerical[][]{{c.add(M), b, V_cp, V_b}});
    		}
    		else
    		{
    			Int V_c = variation(S, x, c);
    			if(V_a.equals(V_c.add(Int.ONE)))
    				result = Set.add(result, new Numerical[][]{{a, c}});
    			if(V_a.compareTo(V_c.add(Int.ONE)) > 0)
    				work = Set.add(work, new Numerical[][]{{a, c, V_a, V_c}});
    			if(V_b.equals(V_c.sub(Int.ONE)))
    				result = Set.add(result, new Numerical[][]{{c, b}});
    			if(V_b.compareTo(V_c.sub(Int.ONE)) < 0)
    				work = Set.add(work, new Numerical[][]{{c, b, V_c, V_b}});
    		}
    	}
    	return result;
    }
    
    public static Numerical[][] isolate_roots(Expr p, Expr x, Numerical dx)
    {
    	Numerical[][] iso = isolate_roots(p, x);
    	boolean done = false;
    	while(!done)
    	{
    		boolean small_enough = true;
    		for(int i = 0;i<iso.length;i++)
    		{
    			Numerical a = iso[i][0];
    			Numerical b = iso[i][1];
    			if(b.sub(a).compareTo(dx) > 0)
    			{
    				small_enough = false;
    				Numerical c = b.add(a).div(Int.TWO);
    				Expr p_c = Poly.horner_evaluate(p, x, c);
    				if(p_c.equals(Int.ZERO))
    					iso[i] = new Numerical[]{c, c};
    				else
    				{
    					Expr p_a = Poly.horner_evaluate(p, x, a);
    					if((Simplification.is_positive(p_c) && Simplification.is_negative(p_a)) 
    							|| (Simplification.is_positive(p_a) && Simplification.is_negative(p_c)))
    						iso[i] = new Numerical[]{a, c};
    					else
    					{
    						Expr p_b = Poly.horner_evaluate(p, x, b);
        					if((Simplification.is_positive(p_c) && Simplification.is_negative(p_b)) 
        							|| (Simplification.is_positive(p_b) && Simplification.is_negative(p_c)))
        						iso[i] = new Numerical[]{c, b};
        					else
        						throw new IllegalArgumentException("Cannot determine sign of "+p_c+" or "+p_a+" or "+p_b);
    					}
    				}
    			}
    		}
    		if(small_enough)
    			done = true;
    	}
    	return iso;
    }
    
   
}
