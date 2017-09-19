package algebra;

import calculus.Diff;
import polynomial.BasicPoly;
import polynomial.Cancel;
import polynomial.GCD;
import polynomial.GCDAlgebraicNumberField;
import polynomial.Poly;
import polynomial.Resultant;
import Expression.Expr;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;

public class AlgebraicNumberField 
{
	
	public static Expr simplify_algebraic_expression(Expr u, Expr[] p, Expr[] a)
	{
		if(u.isInt() || u.isRational())
			return u;
		if(u.isSum())
		{
			Expr v = u.get(0);
			Expr w = u.sub(v);
			v = simplify_algebraic_expression(v, p, a);
			w = simplify_algebraic_expression(w, p, a);
			return add(v, w, p, a);
		}
		if(u.isProduct())
		{
			Expr v = u.get(0);
			Expr w = u.div(v);
			v = simplify_algebraic_expression(v, p, a);
			w = simplify_algebraic_expression(w, p, a);
			if(w.equals(Int.ZERO))
				return Constant.UNDEFINED;
			return multiply(v, w, p, a);
		}
		if(u.isPower())
		{
			Expr b = u.get(0);
			Int e = (Int)u.get(1);
			b = simplify_algebraic_expression(b, p, a);
			return power(b, e, p, a);
		}
		return simplify_algebraic_number(u, p, a);
	}

	public static Expr simplify_algebraic_number(Expr u, Expr[] p, Expr[] a)
	{
		if(p.length == 0)
			return u;
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] p_r = Set.rest(p);
		Expr[] a_r = Set.rest(a);
		return polynomial_remainder(simplify_coef(Algebra.expand(u), a_1, p_r, a_r), p_1, a_1, p_r, a_r);
	}
	
	public static Expr multiply(Expr u, Expr v, Expr[] p, Expr[] a)
	{
		if(p.length == 0)
			return Algebra.expand(u.mul(v));
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] p_r = Set.rest(p);
		Expr[] a_r = Set.rest(a);
		return polynomial_remainder(simplify_coef(Algebra.expand(u.mul(v)), a_1, p_r, a_r), p_1, a_1, p_r, a_r);
	}
	
	public static Expr add(Expr u, Expr v, Expr[] p, Expr[] a)
	{
		if(p.length == 0)
			return u.add(v);
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] p_r = Set.rest(p);
		Expr[] a_r = Set.rest(a);
		return polynomial_remainder(simplify_coef(Algebra.expand(u.add(v)), a_1, p_r, a_r), p_1, a_1, p_r, a_r);
	}
	
	public static Expr subtract(Expr u, Expr v, Expr[] p, Expr[] a)
	{
		if(p.length == 0)
			return Algebra.expand(u.sub(v));
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] p_r = Set.rest(p);
		Expr[] a_r = Set.rest(a);
		return polynomial_remainder(simplify_coef(Algebra.expand(u.sub(v)), a_1, p_r, a_r), p_1, a_1, p_r, a_r);
	}
	
	public static Expr inverse(Expr u, Expr[] p, Expr[] a)
	{
		if(u.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(p.length == 0)
			return Int.ONE.div(u);
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] A = GCDAlgebraicNumberField.polynomial_extended_gcd(u, p_1, a_1, Set.rest(p), Set.rest(a));
		if(A[0].equals(Int.ONE))
		    return A[1];
		return null; //No multiplicative inverse - polynomial reducible
	}
	
	public static Expr divide(Expr u, Expr v, Expr[] p, Expr[] a)
	{
		Expr inverse = inverse(v, p, a);
		return multiply(u, inverse, p, a);
	}
	
	public static Expr power(Expr u, Int n, Expr[] p, Expr[] a)
	{
		if(n.equals(Int.ZERO))
			return Int.ONE;
		if(n.isPositive())
		{
			Expr d = Int.ONE;
			for(Int i = Int.ONE;i.compareTo(n)<=0;i = i.add(Int.ONE))
				d = multiply(d, u, p, a);
			return d;
		}
        n = n.mul(Int.NONE);
		Expr d = Int.ONE;
		for(Int i = Int.ONE;i.compareTo(n)<=0;i = i.add(Int.ONE))
			d = multiply(d, u, p, a);
		return inverse(d, p, a);
	}
	
	public static Expr simplify_coef(Expr u, Expr x, Expr[] p, Expr[] a)
	{
		u = Algebra.expand(u);
		if(u.equals(Int.ZERO))
			return Int.ZERO;
        Int n = Poly.degree(u, x);
        Expr s = Int.ZERO;
        for(Int i = Int.ZERO;i.compareTo(n)<=0;i = i.add(Int.ONE))
        {
        	Expr v = Poly.coefficient_poly(u, x, i);
        	v = simplify_algebraic_number(v, p, a);
        	s = s.add(v.mul(x.pow(i)));
        }
        return s;
	}
	
	public static Expr simplify_coef(Expr u, Expr[] x, Expr[] p, Expr[] a)
	{
		if(x.length == 1)
			return simplify_coef(u, x[0], p, a);
		u = Algebra.expand(u);
		if(u.equals(Int.ZERO))
			return Int.ZERO;
        Int n = Poly.degree(u, x[0]);
        Expr[] r = Set.rest(x);
        Expr s = Int.ZERO;
        for(Int i = Int.ZERO;i.compareTo(n)<=0;i = i.add(Int.ONE))
        {
        	Expr v = Poly.coefficient_poly(u, x[0], i);
        	v = simplify_coef(v, r, p, a);
        	s = s.add(v.mul(x[0].pow(i)));
        }
        return s;
	}
	
	public static Expr[] polynomial_division(Expr u, Expr v, Expr x, Expr[] p, Expr[] a)
	{
		if(p.length == 0)
			return BasicPoly.polynomial_division(u, v, x);
		Expr q = Int.ZERO;
		Expr r = u;
		Int m = Poly.degree(r, x);
		Int n = Poly.degree(v, x);
		Expr lcv = Poly.coefficient_poly(v, x, n);
		while(m.compareTo(n)>=0)
		{
			Expr lcr = Poly.leading_coef(r, x);
			Expr s = divide(lcr, lcv, p, a);
			q = q.add(s.mul(x.pow(m.sub(n))));
			r = Algebra.expand(r.sub(lcr.mul(x.pow(m))).sub(v.sub(lcv.mul(x.pow(n))).mul(s).mul(x.pow(m.sub(n)))));
			r = simplify_coef(r, x, p, a);
			m = Poly.degree(r, x);
		}
		return new Expr[]{q, r};
	}
	
	public static Expr polynomial_remainder(Expr u, Expr v, Expr x, Expr[] p, Expr[] a)
	{
		return polynomial_division(u, v, x, p, a)[1];
	}
	
	public static Expr polynomial_quotient(Expr u, Expr v, Expr x, Expr[] p, Expr[] a)
	{
		return polynomial_division(u, v, x, p, a)[0];
	}
	
	public static Expr make_monic(Expr u, Expr x, Expr[] p, Expr[] a)
	{
		if(p.length == 0)
			return BasicPoly.make_monic(u, x);
		Expr lc = Poly.leading_coef(u, x);
		return simplify_coef(u.mul(inverse(lc, p, a)), x, p, a);
	}
	
	public static Expr rational_simplify_sv(Expr u, Expr x, Expr[] p, Expr[] a)
	{
		Expr v = Algebra.rationalize_expand(u);
		Expr[] nd = Algebra.NumeratorDenominator(v);
		Expr n = simplify_coef(nd[0], x, p, a);
		Expr d = simplify_coef(nd[1], x, p, a);
		if(d.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(d.equals(Int.ONE))
			return n;
		Expr gcd = GCDAlgebraicNumberField.polynomial_gcd(n, d, x, p, a);
		Expr r = polynomial_quotient(n, gcd, x, p, a);
		Expr s = polynomial_quotient(d, gcd, x, p, a);
		Expr lcr = Poly.leading_coef(r, x);
		Expr lcs = Poly.leading_coef(s, x);
		Expr lcr_i = inverse(lcr, p, a);
		Expr lcs_i = inverse(lcs, p, a);
		r = simplify_coef(r.mul(lcr_i), x, p, a);
		s = simplify_coef(s.mul(lcs_i), x, p, a);
		return simplify_algebraic_number(lcr.mul(lcs_i), p, a).mul(r.div(s));
	}
	
	public static Expr find_polynomial(Expr u, Expr x, Expr y)
	{
		if(Poly.is_poly_Q(u, x))
			return y.sub(u);
		if(u.equals(Constant.I))
			return y.pow(Int.TWO).add(Int.ONE);
		Expr w = Simplification.getNewVariables(1, u, x, y)[0];
		if(u.isPower())
		{
			Expr base = u.get(0);
			Expr exponent = u.get(1);
			Expr[] nd = Algebra.NumeratorDenominator(exponent);
			Int n = (Int)nd[0];
			Int d = (Int)nd[1];
			if(base.isInt())
				return y.pow(d).sub(base.pow(n));
			Expr p = find_polynomial(base, x, y).substitute(y, w);
			if(Simplification.is_positive(exponent))
				return Resultant.modular_resultant_rationals(p, y.pow(d).sub(w.pow(n)), new Expr[]{w, y, x});
			else
			{
				Expr r = Resultant.modular_resultant_rationals(p, y.pow(d).sub(w.pow(n.abs())), new Expr[]{w, y, x}).substitute(y, w);
				return Resultant.modular_resultant_rationals(y.mul(w).sub(Int.ONE), r, new Expr[]{w, y, x});
			}
		}
		if(u.isSum())
		{
			Expr r = find_polynomial(u.get(0), x, y);
			for(int i = 1;i<u.length();i++)
			{
				Expr p = find_polynomial(u.get(i), x, y);
				Expr q = Algebra.expand(p.substitute(y, y.sub(w)));
				r = Resultant.modular_resultant_rationals(q, r.substitute(y, w), new Expr[]{w, y, x});
			}
			return r;
		}
		if(u.isProduct())
		{
			Expr r = find_polynomial(u.get(0), x, y);
			for(int i = 1;i<u.length();i++)
			{
				Expr p = find_polynomial(u.get(i), x, y);
				Int m = Poly.degree(p, y);
				Expr q = Algebra.expand(w.pow(m).mul(p.substitute(y, y.div(w))));
				r = Resultant.modular_resultant_rationals(q, r.substitute(y, w), new Expr[]{w, y, x});
			}
			return r;
		}
		return null;
	}
	
	public static boolean is_explicit_algebraic_number(Expr u)
	{
		if(u.isNumerical())
			return true;
		if(u.equals(Constant.I))
			return true;
		if(u.isSum() || u.isProduct())
		{
			for(int i = 0;i<u.length();i++)
				if(!is_explicit_algebraic_number(u.get(i)))
					return false;
			return true;
		}
		if(u.isPower())
		{
			if(u.get(1).isNumerical() && is_explicit_algebraic_number(u.get(0)))
				return true;
		}
		return false;
	}
	
	public static Expr[] square_free_norm(Expr f, Expr x, Expr p, Expr alpha)
	{
		Int s = Int.ZERO;
		Expr g = f;
		Expr N = Resultant.multivariate_resultant(g, p, new Expr[]{alpha, x}, "Q");
		Expr gcd = GCD.multivariate_gcd(N, Algebra.expand(Diff.derivative(N, x)), "Q");
		while(!Poly.degree(gcd, x).equals(Int.ZERO))
		{
			s = s.add(Int.ONE);
			g = simplify_coef(Algebra.expand(g.substitute(x.sub(alpha), alpha)), x, new Expr[]{p}, new Expr[]{alpha});
			N = Resultant.multivariate_resultant(g, p, new Expr[]{alpha, x}, "Q");
			gcd = GCD.multivariate_gcd(N, Algebra.expand(Diff.derivative(N, x)), "Q");
		}
		return new Expr[]{g, s, N};
	}
	
	public static Expr simplify_in_A(Expr u, Expr fx)
	{
		if(u.isSymbolic())
			return u;
		Expr[] ops = new Expr[u.length()];
		for(int i = 0;i<u.length();i++)
		{
			ops[i] = simplify_in_A(u.get(i), fx);
		}
		Expr v = Simplification.simplify_recursive(new Expr(u.getOperator(), ops));
		Expr[] nd = Algebra.NumeratorDenominator(v);
		if(!nd[1].equals(Int.ONE))
		{
		    Expr s = simplify_in_A(nd[0], fx);
		    Expr x = simplify_in_A(nd[1], fx);
		    if(is_explicit_algebraic_number(x))
		    {
		    	Expr y = Simplification.getNewVariables(1, u)[0];
		    	Expr t = Simplification.getNewVariables(1, u, y)[0];
		    	Expr mp = find_polynomial(x, t, y);
		    	Expr inv = inverse(y, new Expr[]{mp}, new Expr[]{y});
		    	if(inv == null)
		    		return v;
		    	return Algebra.expand(inv.substitute(y, x).mul(s));
		    }
		    if(!fx.equals(Constant.VOID))
		    {
		    	if(AlgebraicFunctionField.is_explicit_algebraic_function(x, fx))
		    	{
		    		Expr y = Simplification.getNewVariables(1, u)[0];
		    		Expr mp = find_polynomial(x, fx, y);
		    		Expr inv = AlgebraicFunctionField.inverse(y, new Expr[]{mp}, new Expr[]{y}, fx);
		    		if(inv == null)
		    			return v;
		    		return Algebra.cancel(Algebra.cancel(inv.mul(s)).substitute(y, x));
		    	}
		    }
		}
		if(v.isProduct())
			return Algebra.cancel(v);
		if(v.isPower() && v.get(1).isInt())
		{
			if(fx.equals(Constant.VOID))
				return Algebra.expand(v);
			else
				return Algebra.cancel(v);
		}
		return v;
	}
	
	
	public static Expr[] pseudo_division_anf(Expr u, Expr v, Expr x, Expr[] pe, Expr[] a)
	{
		Expr p = Int.ZERO;
		Expr s = u;
		Int m = Poly.degree(s, x);
		Int n = Poly.degree(v, x);
		Int delta = Int.max(m.sub(n).add(Int.ONE), Int.ZERO);
		Expr lcv = Poly.coefficient_poly(v, x, n);
		Int sigma = Int.ZERO;
		while(m.compareTo(n) >= 0)
		{
			Expr lcs = Poly.coefficient_poly(s, x, m);
			p = simplify_coef(lcv.mul(p).add(lcs.mul(x.pow(m.sub(n)))), x, pe, a);
			s = simplify_coef(lcv.mul(s).sub(lcs.mul(v).mul(x.pow(m.sub(n)))), x, pe, a);
			sigma = sigma.add(Int.ONE);
			m = Poly.degree(s, x);
		}
		return new Expr[]{simplify_coef(lcv.pow(delta.sub(sigma)).mul(p), x, pe, a),
				simplify_coef(lcv.pow(delta.sub(sigma)).mul(s), x, pe, a)};
	}
	
	public static Expr[] multivariate_division_anf(Expr u, Expr v, Expr[] L, Expr[] p, Expr[] a)
	{
		if(L.length == 0)
		{
			Expr f = divide(u, v, p, a);
				return new Expr[]{f, Int.ZERO};
		}
		else
		{
			Expr x = L[0];
			Expr[] rest = new Expr[L.length-1];
			for(int i = 0;i<rest.length;i++)
				rest[i] = L[i+1];
			Expr r = u;
			Int m = Poly.degree(u, x);
			Int n = Poly.degree(v, x);
			Expr q = Int.ZERO;
			Expr lcv = Poly.coefficient_poly(v, x, n);
			while(m.compareTo(n)>=0)
			{
				Expr lcr = Poly.coefficient_poly(r, x, Poly.degree(r, x));
				Expr[] d = multivariate_division_anf(lcr, lcv, rest, p, a);
				if(!d[1].equals(Int.ZERO))
					return new Expr[]{simplify_coef(q, L, p, a), r};
				else
				{
					Expr c = d[0];
					if(!m.equals(Int.NONE))
					{
						q = simplify_coef(q.add(c.mul(x.pow(m.sub(n)))), L, p, a);
						r = simplify_coef(r.sub(c.mul(v).mul(x.pow(m.sub(n)))), L, p, a);
					}
					m = Poly.degree(r, x);
				}
			}
			return new Expr[]{q, r};
		}
	}
	
}
