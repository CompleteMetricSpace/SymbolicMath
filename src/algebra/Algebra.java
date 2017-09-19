package algebra;

import java.util.Vector;

import polynomial.BasicPoly;
import polynomial.GCD;
import polynomial.Poly;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;
import Symbolic.Numerical;
import Symbolic.Rational;

public class Algebra 
{

	public static Expr expand(Expr u)
	{
		if(u.isSum())
		{
			Expr v = u.get(0);
			Expr[] r = u.rest();
			return expand(v).add(expand(Simplification.simplify_recursive(new Expr(Operator.ADD, r))));
		}
		if(u.isProduct())
		{
			Expr v = u.get(0);
			Expr[] r = u.rest();
			return expand_product(expand(v),expand(Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, r))));
		}
		if(u.isPower())
		{
			Expr b = u.get(0);
			Expr e = u.get(1);
			if(e.isInt() && ((Int)e).compareTo(Int.TWO)>=0)
			{
				return expand_power(expand(b), (Int)e);
			}	
		}
		return u;
	}

	private static Expr expand_power(Expr u, Int n)
	{
		if(u.getOperator().equals(Operator.ADD) && n.isPositive())
		{
			Expr[] f_1 = new Expr[u.length()/2];
	    	Expr[] f_2 = new Expr[u.length()-u.length()/2];
	    	
	    	for(int i = 0;i<u.length();i++)
	    	{
	    		if(i<f_1.length)
	    			f_1[i] = u.getOperands()[i];
	    		else
	    			f_2[i-f_1.length] = u.getOperands()[i];
	    	}
	    	Expr exp_1 = f_1.length == 1?f_1[0]:new Expr(Operator.ADD, f_1);
	    	Expr exp_2 = f_2.length == 1?f_2[0]:new Expr(Operator.ADD, f_2);
			
			Expr[] s = new Expr[n.toInt()+1];
			Int n_fac = n.factorial();
			Int k_fac = Int.ONE;
			
			for(Int k = Int.ZERO;k.compareTo(n) <= 0;k = k.add(Int.ONE))
			{
				if(!k.equals(Int.ZERO))
					k_fac = k.mul(k_fac);
				Expr c = n_fac.division(k_fac.mul(n.sub(k).factorial()));
				s[k.toInt()] = expand_product(expand(c.mul(expand_power(exp_1,n.sub(k)))), expand_power(exp_2, k));
			}
			return Simplification.simplify_recursive(new Expr(Operator.ADD, s));
		}
		return u.pow(n);
	}

	private static Expr expand_power_binary(Expr u, Int n)
	{
		if(u.getOperator().equals(Operator.ADD) && n.isPositive())
		{
			if(n.equals(Int.ONE))
				return u;
			if(!n.isOdd())
			{
				return expand_power_binary(expand_power(u, Int.TWO), n.divide(Int.TWO));
			}
			else
			{
				return expand_product(u, expand_power_binary(expand_power(u, Int.TWO), n.sub(Int.ONE).divide(Int.TWO)));
			}
		}
		return u.pow(n);
	}
	
	private static Expr expand_product(Expr u, Expr v)
	{
		if(u.isSum())
		{
			Expr f = u.get(0);
			return expand_product(f, v).add(expand_product(u.sub(f), v));
		}
		if(v.isSum())
		{
			return expand_product(v, u);
		}
		return u.mul(v);
	}
	
	public static Expr weak_expand(Expr u)
	{
		if(u.isProduct())
		{
			Expr v = u.get(0);
			Expr[] r = u.rest();
			return expand_product(weak_expand(v), weak_expand(Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, r))));
		}
		if(u.isPower())
		{
			Expr b = u.get(0);
			Expr e = u.get(1);
			if(e.isInt() && ((Int)e).compareTo(Int.TWO)>=0)
			{
				return expand_power(b, (Int)e);
			}	
		}
		return u;
	}
	
	public static Expr[] NumeratorDenominator(Expr u)
    {
		return NumeratorDenominator(u, true);
    }
	
	public static Expr[] NumeratorDenominator(Expr u, boolean fraction)
    {
        if(u.isRational())
        {
        	if(fraction)
        	    return new Expr[]{((Rational)u).getNumerator(), ((Rational)u).getDenominator()};
        	else
        		return new Expr[]{u, Int.ONE};
        }
        if(u.isPower())
        {
        	Expr exponent = u.get(1);
        	if(exponent.isNumerical() && ((Numerical)exponent).compareTo(Int.ZERO)<0)
        		return new Expr[]{Int.ONE, u.get(0).pow(Int.NONE.mul(exponent))};
        }
        if(u.isProduct())
        {
        	Expr v = u.get(0);
        	Expr[] r = u.rest();
        	Expr[] nd_u_v = NumeratorDenominator(Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, r)), fraction);
        	Expr[] nd_v = NumeratorDenominator(v, fraction);
        	return new Expr[]{nd_u_v[0].mul(nd_v[0]), nd_u_v[1].mul(nd_v[1])};
        }
        return new Expr[]{u, Int.ONE};
    }
	
	public static Expr rationalize(Expr u)
	{
		if(u.isPower())
		{
			return rationalize(u.get(0)).pow(u.get(1));
		}
		if(u.isProduct())
		{
			Expr f = u.get(0);
			return rationalize(f).mul(rationalize(u.div(f)));
		}
		if(u.isSum())
		{
			Expr f = u.get(0);
			return rationalize_sum(rationalize(f), rationalize(u.sub(f)));
		}
		return u;
	}
	
	public static Expr rationalize_sum(Expr u, Expr v)
	{
		Expr[] nd_u = NumeratorDenominator(u);
		Expr[] nd_v = NumeratorDenominator(v);
		if(nd_u[1].equals(Int.ONE) && nd_v[1].equals(Int.ONE))
			return u.add(v);
		else
			return rationalize_sum(nd_u[0].mul(nd_v[1]), nd_u[1].mul(nd_v[0])).div(nd_u[1].mul(nd_v[1]));
	}
	
	public static Expr rationalize_expand(Expr u)
	{
		Expr[] nd = NumeratorDenominator(rationalize(u));
		return expand(nd[0]).div(expand(nd[1]));
	}
	
	public static Expr collect(Expr u, Expr... x)
	{
		if(!u.isSum())
		{
			if(Poly.coef_var_monomial(u, x) == null)
				return null;
			return u;
		}
		if(Set.member(x, u))
			return u;
		Vector<Expr[]> T = new Vector<>();
		for(int i = 0;i<u.length();i++)
		{
			Expr[] f = Poly.coef_var_monomial(u.get(i), x);
			if(f == null)
				return null;
			int j = 0;
			boolean combined = false;
			while(!combined && j<T.size())
			{
				if(T.get(j)[1].equals(f[1]))
				{
					T.set(j, new Expr[]{T.get(j)[0].add(f[0]), f[1]});
					combined = true;
				}
				j = j+1;
			}
			if(!combined)
				T.add(f);
		}
		Expr v = Int.ZERO;
		for(int i = 0;i<T.size();i++)
			v = v.add(Simplification.simplify_product(new Expr(Operator.MULTIPLY, T.get(i))));
		return v;
	}
	
	public static Expr rational_simplify_sv(Expr u, Expr x)
	{
		Expr v = rationalize_expand(u);
		Expr[] nd = NumeratorDenominator(v);
		Expr n = nd[0];
		Expr d = nd[1];
		if(d.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(d.equals(Int.ONE))
			return n;
		Expr gcd = GCD.polynomial_gcd(n, d, x);
		Expr r = BasicPoly.polynomial_quotient(n, gcd, x);
		Expr s = BasicPoly.polynomial_quotient(d, gcd, x);
		Expr lcr = Poly.leading_coef(r, x);
		Expr lcs = Poly.leading_coef(s, x);
		r = expand(r.div(lcr));
		s = expand(s.div(lcs));
		return lcr.div(lcs).mul(r.div(s));
	}
	
	public static Expr rational_simplify_mv(Expr u, Expr[] x)
	{
		Expr v = rationalize_expand(u);
		Expr[] nd = NumeratorDenominator(v);
		Expr n = nd[0];
		Expr d = nd[1];
		if(d.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(d.equals(Int.ONE))
			return n;
		Int lcm_n = Poly.coefficient_lcm(n, x);
		Int lcm_d = Poly.coefficient_lcm(d, x);
		n = n.mul(lcm_n);
		d = d.mul(lcm_d);
		Expr gcd = GCD.multivariate_gcd(n, d, x, "Z");
		Expr r = BasicPoly.multivariate_division(n, gcd, x, "Z")[0];
		Expr s = BasicPoly.multivariate_division(d, gcd, x, "Z")[0];
	    r = r.mul(lcm_d);
	    s = s.mul(lcm_n);
	    Int lc = (Int) Poly.leading_coef(s, x);
	    if(lc.compareTo(Int.ZERO) < 0)
	    {
	    	r = r.mul(Int.NONE);
	    	s = s.mul(Int.NONE);
	    }
		return r.div(s);
	}
	
	public static Expr cancel(Expr u)
	{
		Expr v = rationalize_expand(u);
		Expr[] nd = NumeratorDenominator(v);
		Expr n = nd[0];
		Expr d = nd[1];
		if(n.isNumerical() && d.isNumerical())
			return n.div(d);
		if(d.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(d.equals(Int.ONE))
			return n;
		Expr[] vars = Set.union(Poly.variables(n), Poly.variables(d));
		Expr[] x = Simplification.getNewVariables(vars.length, n, d);
		n = Algebra.expand(Simplification.simplify_recursive(n.substitute(vars, x)));
		d = Algebra.expand(Simplification.simplify_recursive(d.substitute(vars, x)));
		Int lcm_n = Poly.coefficient_lcm(n, x);
		Int lcm_d = Poly.coefficient_lcm(d, x);
		n = n.mul(lcm_n);
		d = d.mul(lcm_d);
		Expr gcd = GCD.multivariate_gcd(n, d, x, "Z");
		Expr r = BasicPoly.multivariate_division(n, gcd, x, "Z")[0];
		Expr s = BasicPoly.multivariate_division(d, gcd, x, "Z")[0];
		Int gcd_lcm = Int.gcd(lcm_n, lcm_d);
	    r = r.mul(lcm_d.divide(gcd_lcm));
	    s = s.mul(lcm_n.divide(gcd_lcm));
	    Int lc = (Int) Poly.leading_coef(s, x);
	    if(lc.compareTo(Int.ZERO) < 0)
	    {
	    	r = r.mul(Int.NONE);
	    	s = s.mul(Int.NONE);
	    }
	    r = Algebra.expand(Simplification.simplify_recursive(r.substitute(x, vars)));
		s = Algebra.expand(Simplification.simplify_recursive(s.substitute(x, vars)));
		Expr[] vars_new = Set.union(Poly.variables(r), Poly.variables(s));
		//Check whether new polynomials after substitution are still prime
		if(vars_new.length != vars.length)
			return cancel(r.div(s));
		return r.div(s);
	}
	
	public static Expr cancel_fractional_exponent(Expr u)
	{
		Expr v = rationalize_expand(u);
		Expr[] nd = NumeratorDenominator(v);
		Expr n = nd[0];
		Expr d = nd[1];
		Expr[] vars = Set.union(Poly.variables_fractional_exponent(n), Poly.variables_fractional_exponent(d));
		if(vars.length == 0)
			return n.div(d);
		Expr[] x = Simplification.getNewVariables(vars.length, n, d);
		n = Algebra.expand(Simplification.simplify_recursive(n.substitute(vars, x)));
		d = Algebra.expand(Simplification.simplify_recursive(d.substitute(vars, x)));
		Int[] lcm = new Int[x.length];
		for(int i = 0;i<lcm.length;i++)
			lcm[i] = Int.lcm(get_fraction_exponent_lcm(n, x[i]), get_fraction_exponent_lcm(d, x[i]));
		Expr[] x_p = new Expr[x.length];
		for(int i = 0;i<x_p.length;i++)
			x_p[i] = x[i].pow(lcm[i]);
		Expr[] x_q = new Expr[x.length];
		for(int i = 0;i<x_q.length;i++)
			x_q[i] = x[i].pow(Int.ONE.div(lcm[i]));
		Expr g = Simplification.simplify_recursive(n.substitute(x, x_p));
		Expr h = Simplification.simplify_recursive(d.substitute(x, x_p));
		for(int i = 0;i<x.length;i++)
		{
			g = Simplification.simplify_power_fraction(g, x[i]);
			h = Simplification.simplify_power_fraction(h, x[i]);
		}
		Expr c = Algebra.cancel(g.div(h));
		Expr cancel = Simplification.simplify_recursive(c.substitute(x, x_q));
		cancel = Simplification.simplify_recursive(cancel.substitute(x, vars));
		//Check if new polynomials are still prime
		if(!c.equals(g.div(h)))
			return Algebra.cancel(cancel);
		return cancel;
	}
	
	public static Expr[] partial_fraction_1(Expr u, Expr v1, Expr v2, Expr x)
	{
		Expr[] s = GCD.polynomial_extended_gcd(v1, v2, x);
		Expr u1 = BasicPoly.polynomial_remainder(Algebra.expand(s[2].mul(u)), v1, x);
		Expr u2 = BasicPoly.polynomial_remainder(Algebra.expand(s[1].mul(u)), v2, x);
		return new Expr[]{u1, u2};
	}
	
	public static Expr[] partial_fraction_2(Expr u, Expr[] v, Expr x)
	{
		if(v.length == 1)
			return new Expr[]{u};
		Expr f = v[0];
		Expr[] r = Set.rest(v);
		Expr rr = Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, r));
		Expr[] s = partial_fraction_1(u, expand(f), expand(rr), x);
		Expr u1 = s[0];
		Expr w = s[1];
		Expr[] ret = partial_fraction_2(w, r, x);
		return Set.add(new Expr[]{u1}, ret);
	}
	
	public static Expr[][] partial_fraction_3(Expr u, Expr[] p, Int[] n, Expr x)
	{
		Expr[] pow = new Expr[p.length];
		for(int i = 0;i<pow.length;i++)
		{
			pow[i] = Algebra.expand(p[i].pow(n[i]));
		}
		Expr[] pf = partial_fraction_2(u, pow, x);
		Expr[][] q = new Expr[pf.length][];
		Expr t = Simplification.getNewVariables(1, Set.add(p, new Expr[]{u, x}))[0];
		for(int i = 0;i<q.length;i++)
		{
			Expr u_i = pf[i];
			Expr poly = BasicPoly.polynomial_expansion(u_i, p[i], x, t);
			Int m = n[i];
			q[i] = new Expr[m.toInt()];
			for(Int j = Int.ZERO;j.compareTo(m)<0;j = j.add(Int.ONE))
			{
				Expr coef = Poly.coefficient_poly(poly, t, j);
				q[i][(q[i].length-1)-j.toInt()] = coef;
			}
		}
		return q;
	}
	
	public static Expr[] max(Expr[] u)
	{
		if(u.length == 1)
			return u;
		Expr f = u[0];
		Expr[] R = max(Set.rest(u));
		Vector<Expr> max = new Vector<Expr>();
		for(int i = 0;i<R.length;i++)
		{
			Expr v = R[i];
			Expr d = v.sub(f);
			if(d.isNumerical())
			{
				Numerical D = (Numerical)d;
				if(D.compareTo(Int.ZERO) >= 0)
					return R;
			}
			else
			{
				max.add(v);
			}
		}
		return Set.union(new Expr[]{f}, max.toArray(new Expr[max.size()]));
	}

	public static Int get_fraction_exponent_lcm(Expr u, Expr x) 
	{
		if(u.isSymbolic())
			return Int.ONE;
		if(u.isPower())
		{
			Expr b = u.get(0);
			Expr e = u.get(1);
			if(b.equals(x))
			{
				if(e.isInt())
					return Int.ONE;
				if(e.isRational())
				{
					return ((Rational)e).getDenominator();
				}
			}
		}
		Int n = Int.ONE;
		for(int i = 0;i<u.length();i++)
			n = Int.lcm(n, get_fraction_exponent_lcm(u.get(i), x));
		return n;
	}
	
	public static Expr replace_power_by_exp(Expr u, Expr x)
	{
		if(u.isSymbolic())
			return u;
		Expr[] v = new Expr[u.length()];
		for(int i = 0;i<u.length();i++)
			v[i] = replace_power_by_exp(u.get(i), x);
		Expr U = Simplification.simplify_recursive(new Expr(u.getOperator(), v));
		if(U.isPower() && !U.get(1).isFreeOf(x))
			return U.get(0).log().mul(U.get(1)).exp();
		return U;
	}

	public static Expr expand_full(Expr a) 
	{
		if(a.isSymbolic())
			return a;
		Expr[] n = new Expr[a.length()];
		for(int i = 0;i<n.length;i++)
			n[i] = expand_full(a.get(i));
		return expand(new Expr(a.getOperator(), n));
	}
	
}
