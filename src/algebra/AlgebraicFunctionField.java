package algebra;

import polynomial.BasicPoly;
import polynomial.Cancel;
import polynomial.GCD;
import polynomial.Poly;
import Expression.Expr;
import Simplification.Set;
import Symbolic.Constant;
import Symbolic.Int;

public class AlgebraicFunctionField
{
	public static Expr simplify_algebraic_expression(Expr u, Expr[] p, Expr[] a, Expr x)
	{
		if(u.isInt() || u.isRational())
			return u;
		if(u.isSum())
		{
			Expr v = u.get(0);
			Expr w = u.sub(v);
			v = simplify_algebraic_expression(v, p, a, x);
			w = simplify_algebraic_expression(w, p, a, x);
			return add(v, w, p, a, x);
		}
		if(u.isProduct())
		{
			Expr v = u.get(0);
			Expr w = u.div(v);
			v = simplify_algebraic_expression(v, p, a, x);
			w = simplify_algebraic_expression(w, p, a, x);
			if(w.equals(Int.ZERO))
				return Constant.UNDEFINED;
			return multiply(v, w, p, a, x);
		}
		if(u.isPower())
		{
			Expr b = u.get(0);
			Int e = (Int)u.get(1);
			b = simplify_algebraic_expression(b, p, a, x);
			return power(b, e, p, a, x);
		}
		return simplify_algebraic_function(u, p, a, x);
	}

	public static Expr simplify_algebraic_function(Expr u, Expr[] p, Expr[] a, Expr x)
	{
		if(p.length == 0)
			return Algebra.cancel(u);
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] p_r = Set.rest(p);
		Expr[] a_r = Set.rest(a);
		return polynomial_remainder(simplify_coef(Algebra.expand(u), a_1, p_r, a_r, x), p_1, a_1, p_r, a_r, x);
	}
	
	public static Expr multiply(Expr u, Expr v, Expr[] p, Expr[] a, Expr x)
	{
		if(p.length == 0)
			return Algebra.cancel(u.mul(v));
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] p_r = Set.rest(p);
		Expr[] a_r = Set.rest(a);
		return polynomial_remainder(simplify_coef(Algebra.expand(u.mul(v)), a_1, p_r, a_r, x), p_1, a_1, p_r, a_r, x);
	}
	
	public static Expr add(Expr u, Expr v, Expr[] p, Expr[] a, Expr x)
	{
		if(p.length == 0)
			return Algebra.cancel(u.add(v));
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] p_r = Set.rest(p);
		Expr[] a_r = Set.rest(a);
		return polynomial_remainder(simplify_coef(Algebra.expand(u.add(v)), a_1, p_r, a_r, x), p_1, a_1, p_r, a_r, x);
	}
	
	public static Expr subtract(Expr u, Expr v, Expr[] p, Expr[] a, Expr x)
	{
		if(p.length == 0)
			return Algebra.cancel(u.sub(v));
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] p_r = Set.rest(p);
		Expr[] a_r = Set.rest(a);
		return polynomial_remainder(simplify_coef(Algebra.expand(u.sub(v)), a_1, p_r, a_r, x), p_1, a_1, p_r, a_r, x);
	}
	
	public static Expr inverse(Expr u, Expr[] p, Expr[] a, Expr x)
	{
		if(u.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(p.length == 0)
			return Algebra.cancel(Int.ONE.div(u));
		Expr p_1 = p[0];
		Expr a_1 = a[0];
		Expr[] A = polynomial_extended_gcd(u, p_1, a_1, Set.rest(p), Set.rest(a), x);
		if(A[0].equals(Int.ONE))
		    return A[1];
		return null; //No multiplicative inverse - polynomial reducible
	}
	
	public static Expr divide(Expr u, Expr v, Expr[] p, Expr[] a, Expr x)
	{
		Expr inverse = inverse(v, p, a, x);
		return multiply(u, inverse, p, a, x);
	}
	
	public static Expr power(Expr u, Int n, Expr[] p, Expr[] a, Expr x)
	{
		if(n.equals(Int.ZERO))
			return Int.ONE;
		if(n.isPositive())
		{
			Expr d = Int.ONE;
			for(Int i = Int.ONE;i.compareTo(n)<=0;i = i.add(Int.ONE))
				d = multiply(d, u, p, a, x);
			return d;
		}
        n = n.mul(Int.NONE);
		Expr d = Int.ONE;
		for(Int i = Int.ONE;i.compareTo(n)<=0;i = i.add(Int.ONE))
			d = multiply(d, u, p, a, x);
		return inverse(d, p, a, x);
	}
	
	public static Expr simplify_coef(Expr u, Expr x, Expr[] p, Expr[] a, Expr var_x)
	{
		u = Algebra.expand(u);
		if(u.equals(Int.ZERO))
			return Int.ZERO;
        Int n = Poly.degree(u, x);
        Expr s = Int.ZERO;
        for(Int i = Int.ZERO;i.compareTo(n)<=0;i = i.add(Int.ONE))
        {
        	Expr v = Poly.coefficient_poly(u, x, i);
        	v = simplify_algebraic_function(v, p, a, var_x);
        	s = s.add(v.mul(x.pow(i)));
        }
        return s;
	}
	
	public static Expr[] polynomial_division(Expr u, Expr v, Expr x, Expr[] p, Expr[] a, Expr var_x)
	{
		if(p.length == 0)
			return Cancel.polynomial_division_cancel(u, v, x);
		Expr q = Int.ZERO;
		Expr r = u;
		Int m = Poly.degree(r, x);
		Int n = Poly.degree(v, x);
		Expr lcv = Poly.coefficient_poly(v, x, n);
		while(m.compareTo(n)>=0)
		{
			Expr lcr = Poly.leading_coef(r, x);
			Expr s = divide(lcr, lcv, p, a, var_x);
			q = q.add(s.mul(x.pow(m.sub(n))));
			r = Algebra.expand(r.sub(lcr.mul(x.pow(m))).sub(v.sub(lcv.mul(x.pow(n))).mul(s).mul(x.pow(m.sub(n)))));
			r = simplify_coef(r, x, p, a, var_x);
			m = Poly.degree(r, x);
		}
		return new Expr[]{q, r};
	}
	
	public static Expr polynomial_remainder(Expr u, Expr v, Expr x, Expr[] p, Expr[] a, Expr var_x)
	{
		return polynomial_division(u, v, x, p, a, var_x)[1];
	}
	
	public static Expr polynomial_quotient(Expr u, Expr v, Expr x, Expr[] p, Expr[] a, Expr var_x)
	{
		return polynomial_division(u, v, x, p, a, var_x)[0];
	}
	
	public static Expr make_monic(Expr u, Expr x, Expr[] p, Expr[] a, Expr var_x)
	{
		if(p.length == 0)
			return BasicPoly.make_monic(u, x);
		Expr lc = Poly.leading_coef(u, x);
		return simplify_coef(u.mul(inverse(lc, p, a, var_x)), x, p, a, var_x);
	}
	
	public static Expr polynomial_gcd(Expr u, Expr v, Expr x, Expr[] p, Expr[] a, Expr var_x)
	{
		if(p.length == 0)
			return Cancel.polynomial_gcd_cancel(u, v, x);
		u = simplify_coef(u, x, p, a, var_x);
		v = simplify_coef(v, x, p, a, var_x);
		if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
			return Int.ZERO;
		Expr U = u;
		Expr V = v;
		while(!V.equals(Int.ZERO))
		{
			Expr R = polynomial_remainder(U, V, x, p, a, var_x);
			U = V;
			V = R;
		}
		return make_monic(U, x, p, a, var_x);
	}
	
	public static Expr[] polynomial_extended_gcd(Expr u, Expr v, Expr x, Expr[] p, Expr[] a, Expr var_x)
	{
		if(p.length == 0)
			return Cancel.polynomial_extended_gcd_cancel(u, v, x);
		if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
			return new Expr[]{Int.ZERO, Int.ZERO, Int.ZERO};
		Expr U = u;
		Expr V = v;
		Expr App = Int.ONE;
		Expr Ap = Int.ZERO;
		Expr Bpp = Int.ZERO;
		Expr Bp = Int.ONE;
		while(!V.equals(Int.ZERO))
		{
			Expr[] qr = polynomial_division(U, V, x, p, a, var_x);
			Expr q = qr[0];
			Expr r = qr[1];
			Expr A = App.sub(q.mul(Ap));
			Expr B = Bpp.sub(q.mul(Bp));
			App = Ap;
			Ap = A;
			Bpp = Bp;
			Bp = B;
			U = V;
			V = r;
		}
		Expr c = Poly.leading_coef(U, x);
		Expr c_i = inverse(c, p, a, var_x);
		App = simplify_coef(App.mul(c_i), x, p, a, var_x);
		Bpp = simplify_coef(Bpp.mul(c_i), x, p, a, var_x);
		U = simplify_coef(U.div(c), x, p, a, var_x);
		return new Expr[]{U, App, Bpp};
	}
	
	public static Expr rational_simplify_sv(Expr u, Expr x, Expr[] p, Expr[] a, Expr var_x)
	{
		Expr v = Algebra.rationalize_expand(u);
		Expr[] nd = Algebra.NumeratorDenominator(v);
		Expr n = simplify_coef(nd[0], x, p, a, var_x);
		Expr d = simplify_coef(nd[1], x, p, a, var_x);
		if(d.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(d.equals(Int.ONE))
			return n;
		Expr gcd = polynomial_gcd(n, d, x, p, a, var_x);
		Expr r = polynomial_quotient(n, gcd, x, p, a, var_x);
		Expr s = polynomial_quotient(d, gcd, x, p, a, var_x);
		Expr lcr = Poly.leading_coef(r, x);
		Expr lcs = Poly.leading_coef(s, x);
		Expr lcr_i = inverse(lcr, p, a, var_x);
		Expr lcs_i = inverse(lcs, p, a, var_x);
		r = simplify_coef(r.mul(lcr_i), x, p, a, var_x);
		s = simplify_coef(s.mul(lcs_i), x, p, a, var_x);
		return simplify_algebraic_function(lcr.mul(lcs_i), p, a, var_x).mul(r.div(s));
	}

	public static boolean is_explicit_algebraic_function(Expr u, Expr x)
	{
		if(u.isNumerical())
			return true;
		if(u.equals(Constant.I))
			return true;
		if(u.equals(x))
			return true;
		if(u.isSum() || u.isProduct())
		{
			for(int i = 0;i<u.length();i++)
				if(!is_explicit_algebraic_function(u.get(i), x))
					return false;
			return true;
		}
		if(u.isPower())
		{
			if(u.get(1).isNumerical() && is_explicit_algebraic_function(u.get(0), x))
				return true;
		}
		return false;
	}
}
