package polynomial;

import java.util.Vector;

import algebra.Algebra;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;
import calculus.Diff;

public class Cancel {

	public static Expr[] square_free_factorization_cancel(Expr a, Expr x)
	{
		Vector<Expr> output = new Vector<Expr>();
		Expr b = Diff.derivative(a, x);
		Expr c = Cancel.polynomial_gcd_cancel(a, b, x);
		Expr w = Cancel.polynomial_division_cancel(a, c, x)[0];
		while(!c.equals(Int.ONE))
		{
			Expr y = Cancel.polynomial_gcd_cancel(w, c, x);
			Expr z = Cancel.polynomial_division_cancel(w, y, x)[0];
			output.add(z);
			w = y;
			c = Cancel.polynomial_division_cancel(c, y, x)[0];
		}
		output.add(w);
		return output.toArray(new Expr[output.size()]);
	}

	public static Expr polynomial_gcd_cancel(Expr u, Expr v, Expr x)
	{
		if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
			return Int.ZERO;
		Expr U = u;
		Expr V = v;
		while(!V.equals(Int.ZERO))
		{
			Expr R = Cancel.polynomial_division_cancel(U, V, x)[1];
			U = V;
			V = R;
		}
		Expr lc = Poly.leading_coef(U, x);
		if(lc.equals(Int.ONE))
			return U;
		else
			return multiply(U, Int.ONE.div(lc), x);
	}

	public static Expr[] polynomial_extended_gcd_cancel(Expr u, Expr v, Expr x)
	{
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
			Expr[] qr = Cancel.polynomial_division_cancel(U, V, x);
			Expr q = qr[0];
			Expr r = qr[1];
			Expr A = subtract(App, multiply(q, Ap, x), x);
			Expr B = subtract(Bpp, multiply(q, Bp, x), x);
			App = Ap;
			Ap = A;
			Bpp = Bp;
			Bp = B;
			U = V;
			V = r;
		}
		Expr c = Poly.leading_coef(U, x);
		App = multiply(App, Int.ONE.div(c), x);
		Bpp = multiply(Bpp, Int.ONE.div(c), x);
		U = multiply(U, Int.ONE.div(c), x);
		return new Expr[]{U, App, Bpp};
	}

	public static Expr[] solve_cancel(Expr a, Expr b, Expr c, Expr x)
	{
		Expr[] gst = polynomial_extended_gcd_cancel(a, b, x);
		Expr s = gst[1], t = gst[2], g = gst[0];
		Expr[] qr = Cancel.polynomial_division_cancel(c, g, x);
		Expr q = qr[0], r = qr[1];
		if(!r.equals(Int.ZERO))
			return null;
		s = multiply(q, s, x);
		t = multiply(q, t, x);
		if(!s.equals(Int.ZERO) && Poly.degree(s, x).compareTo(Poly.degree(b, x)) >= 0)
		{
			qr = Cancel.polynomial_division_cancel(s, b, x);
			q = qr[0]; r = qr[1];
			s = r; t = add(t, multiply(q, a, x), x);
		}
		return new Expr[]{s, t};
	}

	public static Expr[] polynomial_division_cancel(Expr u, Expr v, Expr x)
	{
		Expr q = Int.ZERO;
		Expr r = u;
		Int m = Poly.degree(r, x);
		Int n = Poly.degree(v, x);
		Expr lcv = Poly.coefficient_poly(v, x, n);
		while(m.compareTo(n)>=0)
		{
			Expr lcr = Poly.leading_coef(r, x);
			Expr s = Algebra.cancel(lcr.div(lcv));
			q = add(q, s.mul(x.pow(m.sub(n))), x);
			Expr k = subtract(v, lcv.mul(x.pow(n)), x);
			Expr l = s.mul(x.pow(m.sub(n)));
			r = subtract(subtract(r, lcr.mul(x.pow(m)), x), multiply(k, l, x), x);
			m = Poly.degree(r, x);
		}
		return new Expr[]{q, r};
	}
	
	public static Expr simplify(Expr u, Expr x)
	{
		u = Algebra.expand(u);
		Expr v = Int.ZERO;
		Int n = Poly.degree(u, x);
		for(Int i = Int.ZERO;i.compareTo(n) <= 0;i = i.add(Int.ONE))
		{
			v = v.add(Algebra.cancel(Poly.coefficient_poly(u, x, i)).mul(x.pow(i)));
		}
		return v;
	}
	
	public static Expr simplify_gie(Expr u, Expr x)
	{
		u = Algebra.expand(u);
		Expr v = Int.ZERO;
		Int n = Poly.degree_gie(u, x);
		Int m = Poly.min_degree_gie(u, x);
		for(Int i = m;i.compareTo(n) <= 0;i = i.add(Int.ONE))
		{
			v = v.add(Algebra.cancel(Poly.coefficient_poly_gie(u, x, i)).mul(x.pow(i)));
		}
		return v;
	}
	
	public static Expr simplify(Expr u, Expr... x)
	{
		if(x.length == 1)
			return simplify(u, x[0]);
		Expr t = x[0];
		Expr[] R = Set.rest(x);
		u = Algebra.expand(u);
		Expr v = Int.ZERO;
		Int n = Poly.degree(u, t);
		for(Int i = Int.ZERO;i.compareTo(n) <= 0;i = i.add(Int.ONE))
		{
			Expr smp = simplify(Poly.coefficient_poly(u, t, i), R);
			if(smp.isSum())
			{
				for(int j = 0;j<smp.length();j++)
					v = v.add(smp.get(j).mul(t.pow(i)));
			}
			else
			{
				v = v.add(smp.mul(t.pow(i)));
			}
		}
		return v;
	}
	
	private static Expr[] partial_fraction_1_cancel(Expr u, Expr v1, Expr v2, Expr x)
	{
		Expr[] s = polynomial_extended_gcd_cancel(v1, v2, x);
		Expr u1 = polynomial_division_cancel(Algebra.expand(s[2].mul(u)), v1, x)[1];
		Expr u2 = polynomial_division_cancel(Algebra.expand(s[1].mul(u)), v2, x)[1];
		return new Expr[]{u1, u2};
	}
	
	private static Expr[] partial_fraction_2_cancel(Expr u, Expr[] v, Expr x)
	{
		if(v.length == 1)
			return new Expr[]{u};
		Expr f = v[0];
		Expr[] r = Set.rest(v);
		Expr rr = Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, r));
		Expr[] s = partial_fraction_1_cancel(u, simplify(f, x), simplify(rr, x), x);
		Expr u1 = s[0];
		Expr w = s[1];
		Expr[] ret = partial_fraction_2_cancel(w, r, x);
		return Set.add(new Expr[]{u1}, ret);
	}
	
	public static Expr[][] partial_fraction_3_cancel(Expr u, Expr[] p, Int[] n, Expr x)
	{
		Expr[] pow = new Expr[p.length];
		for(int i = 0;i<pow.length;i++)
		{
			pow[i] = simplify(p[i].pow(n[i]), x);
		}
		Expr[] pf = partial_fraction_2_cancel(u, pow, x);
		Expr[][] q = new Expr[pf.length][];
		Expr t = Simplification.getNewVariables(1, Set.add(p, new Expr[]{u, x}))[0];
		for(int i = 0;i<q.length;i++)
		{
			Expr u_i = pf[i];
			Expr poly = polynomial_expansion_cancel(u_i, p[i], x, t);
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
	
	public static Expr polynomial_expansion_cancel(Expr u, Expr v, Expr x, Expr t)
	{
		if(u.equals(Int.ZERO))
			return Int.ZERO;
		Expr[] d = polynomial_division_cancel(u, v, x);
		Expr q = d[0];
		Expr r = d[1];
		return simplify(t.mul(polynomial_expansion_cancel(q, v, x, t)).add(r), t);
	}
	
	public static Expr multiply_gie(Expr u, Expr v, Expr x)
	{
		if(u.equals(Int.ZERO) || v.equals(Int.ZERO))
			return Int.ZERO;
		Expr p = Int.ZERO;
		Int n = Poly.degree_gie(u, x);
		Int m = Poly.degree_gie(v, x);
		Int l = m.add(n);
		Int q = Poly.min_degree_gie(u, x);
		Int w = Poly.min_degree_gie(v, x);
		Int f = q.add(w);
		for(Int i = f;i.compareTo(l)<=0;i=i.add(Int.ONE))
		{
			Expr s = Int.ZERO;
			for(Int j = f;j.compareTo(i.sub(f))<=0;j = j.add(Int.ONE))
			{
				s = Algebra.cancel(s.add(Poly.coefficient_poly_gie(u, x, j).mul(Poly.coefficient_poly_gie(v, x, i.sub(j)))));
			}
			p = p.add(s.mul(x.pow(i)));
		}
		return p;
	}
	
	public static Expr multiply(Expr u, Expr v, Expr x)
	{
		if(u.equals(Int.ZERO) || v.equals(Int.ZERO))
			return Int.ZERO;
		Expr p = Int.ZERO;
		Int n = Poly.degree(u, x);
		Int m = Poly.degree(v, x);
		Int l = m.add(n);
		for(Int i = Int.ZERO;i.compareTo(l)<=0;i=i.add(Int.ONE))
		{
			Expr s = Int.ZERO;
			for(Int j = Int.ZERO;j.compareTo(i)<=0;j = j.add(Int.ONE))
			{
				s = Algebra.cancel(s.add(Poly.coefficient_poly(u, x, j).mul(Poly.coefficient_poly(v, x, i.sub(j)))));
			}
			p = p.add(s.mul(x.pow(i)));
		}
		return p;
	}
	
	public static Expr add(Expr u, Expr v, Expr x)
	{
		if(u.equals(Int.ZERO))
			return v;
		if(v.equals(Int.ZERO))
			return u;
		Int n = Int.max(Poly.degree(u, x), Poly.degree(v, x));
		Expr p = Int.ZERO;
		for(Int i = Int.ZERO;i.compareTo(n)<=0;i=i.add(Int.ONE))
		{
			p = p.add(Algebra.cancel(Poly.coefficient_poly(u, x, i).add(Poly.coefficient_poly(v, x, i))).mul(x.pow(i)));
		}
		return p;
	}
	
	public static Expr add_gie(Expr u, Expr v, Expr x)
	{
		if(u.equals(Int.ZERO))
			return v;
		if(v.equals(Int.ZERO))
			return u;
		Int n = Int.max(Poly.degree_gie(u, x), Poly.degree_gie(v, x));
		Int m = Int.min(Poly.min_degree_gie(u, x), Poly.min_degree_gie(v, x));
		Expr p = Int.ZERO;
		for(Int i = m;i.compareTo(n)<=0;i=i.add(Int.ONE))
		{
			p = p.add(Algebra.cancel(Poly.coefficient_poly_gie(u, x, i).add(Poly.coefficient_poly_gie(v, x, i))).mul(x.pow(i)));
		}
		return p;
	}
	
	public static Expr subtract(Expr u, Expr v, Expr x)
	{
		if(v.equals(Int.ZERO))
			return u;
		Int n = Int.max(Poly.degree(u, x), Poly.degree(v, x), Int.ZERO);
		Expr p = Int.ZERO;
		for(Int i = Int.ZERO;i.compareTo(n)<=0;i=i.add(Int.ONE))
		{
			p = p.add(Algebra.cancel(Poly.coefficient_poly(u, x, i).sub(Poly.coefficient_poly(v, x, i))).mul(x.pow(i)));
		}
		return p;
	}
	
	public static Expr subtract_gie(Expr u, Expr v, Expr x)
	{
		if(v.equals(Int.ZERO))
			return u;
		Int n = Int.max(Poly.degree_gie(u, x), Poly.degree_gie(v, x));
		Int m = Int.min(Poly.min_degree_gie(u, x), Poly.min_degree_gie(v, x));
		Expr p = Int.ZERO;
		for(Int i = m;i.compareTo(n)<=0;i=i.add(Int.ONE))
		{
			p = p.add(Algebra.cancel(Poly.coefficient_poly_gie(u, x, i).sub(Poly.coefficient_poly_gie(v, x, i))).mul(x.pow(i)));
		}
		return p;
	}
}
