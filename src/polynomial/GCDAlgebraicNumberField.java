package polynomial;

import java.util.Vector;

import Expression.Expr;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;
import Symbolic.Numerical;
import algebra.Algebra;
import algebra.AlgebraicNumberField;

public class GCDAlgebraicNumberField 
{
    static Constant DEFAULT_GCD = Constant.MODULAR;
	
	public static Expr multivariate_gcd(Expr u, Expr v, Expr[] p, Expr[] a)
	{
	    Expr[] vars = Set.complement(Set.union(Poly.variables(u), Poly.variables(v)), a);
	    if(vars.length == 0)
	    	return Int.ONE;
	    Expr[] subs = Simplification.getNewVariables(vars.length, u, v);
	    u = u.substitute(vars, subs);
	    v = v.substitute(vars, subs);
	    Expr gcd = multivariate_gcd(u, v, subs, p, a);
	    return Simplification.simplify_recursive(gcd.substitute(subs, vars));
	}
	
	public static Expr multivariate_gcd(Expr[] u, Expr[] p, Expr[] a)
	{
	    Expr[] vars = new Expr[]{};
	    for(int i = 0;i<u.length;i++)
	    	vars = Set.union(vars, Poly.variables(u[i]));
	    if(vars.length == 0)
	    	return Int.ONE;
	    Expr[] subs = Simplification.getNewVariables(vars.length, u);
	    Expr[] s = new Expr[u.length];
	    for(int i = 0;i<s.length;i++)
	    	s[i] = u[i].substitute(vars, subs);
	   // Expr gcd = multivariate_gcd(s, subs, DEFAULT_GCD, p, a);
	   // return Simplification.simplify_recursive(gcd.substitute(subs, vars));
	    return null;
	}
	
	public static Expr multivariate_gcd(Expr u, Expr v, Expr[] L, Expr[] p, Expr[] a)
	{
	    return null;
		//return multivariate_gcd(u, v, L, K, gcd_method(u, v, L));
	}
	
	public static Expr multivariate_gcd(Expr u, Expr v, Expr[] L, String K, Constant c)
	{
		if(K.equals("Z"))
		{
			if(c.equals(Constant.EUCLID))
				return multivariate_euclid_gcd(u, v, L, "Z");
			if(c.equals(Constant.SUBRESULTANT))
				return multivariate_gcd_sr(u, v, L, "Z");
			if(c.equals(Constant.MODULAR))
				return modular_gcd_integers(u, v, L);
		}
		else
		{
			if(c.equals(Constant.EUCLID))
				return multivariate_euclid_gcd(u, v, L, "Q");
			if(c.equals(Constant.SUBRESULTANT))
				return multivariate_gcd_sr(u, v, L, "Q");
			if(c.equals(Constant.MODULAR))
				return modular_gcd_rationals(u, v, L);
		}
		return null;
	}
	
	private static Expr modular_gcd_rationals(Expr u, Expr v, Expr[] l)
	{
	    // TODO Auto-generated method stub
	    return null;
	}

	private static Expr modular_gcd_integers(Expr u, Expr v, Expr[] l)
	{
	    // TODO Auto-generated method stub
	    return null;
	}

	public static Expr multivariate_gcd(Expr[] u, Expr[] L, String K, Constant c)
	{
		if(u.length == 1)
			return normalize_gcd(u[0], L, K);
		if(u.length == 2)
			return multivariate_gcd(u[0], u[1], L, K, c);
	    Int[] k = new Int[u.length-1];
	    for(int i = 0;i<k.length;i++)
	    	k[i] = Int.random_int(new Int("-1000000"), new Int("1000000"));
	    Expr F = u[0];
	    for(int i = 2;i<u.length;i += 2)
	    	F = Algebra.expand(F.add(k[i-1].mul(u[i])));
	    Expr G = u[1];
	    for(int i = 1;i<u.length;i += 2)
	    	G = Algebra.expand(G.add(k[i-1].mul(u[i])));
	    Expr Hp = multivariate_gcd(F, G, L, K, c);
	    Expr[] s = new Expr[]{};
	    for(int i = 0;i<u.length;i++)
	    {
	    	if(!BasicPoly.multivariate_division(u[i], Hp, L, K)[1].equals(Int.ZERO))
	    		s = Set.add(s, new Expr[]{u[i]});
	    }
	    s = Set.union(s, new Expr[]{Hp});
	    if(s.length > 1)
	    	return multivariate_gcd(s, L, K, c);
	    return s[0];
	}
	
	public static Expr content(Expr u, Expr x, Expr[] R, String K)
	{
		return content(u, x, R, K, DEFAULT_GCD);
	}
	
	public static Expr primitive(Expr u, Expr x)
	{
		Expr[] vars = Set.complement(Poly.variables(u), new Expr[]{x});
	    Expr[] subs = Simplification.getNewVariables(vars.length, u, x);
	    u = u.substitute(vars, subs);
	    Expr pp = primitive(u, x, subs, "Q");
		return pp.substitute(subs, vars);
	}
	
	public static Expr primitive(Expr u, Expr x, Expr[] R, String K)
	{
		Expr cont = content(u, x, R, K);
		return BasicPoly.multivariate_division(u, cont, Set.add(new Expr[]{x}, R), K)[0];
	}
	
	public static Expr content(Expr u, Expr x, Expr[] R, String K, Constant method)
	{
		Int n = Poly.degree(u, x);
		Expr gcd = null;
		for(Int i = Int.ZERO;i.compareTo(n)<=0;i = i.add(Int.ONE))
		{

			Expr c = Poly.coefficient_poly(u, x, i);
			if(i.equals(Int.ZERO))
				gcd = c;
			else
				gcd = multivariate_gcd(gcd, c, R, K, method);
			if(gcd.equals(Int.ONE))
				return Int.ONE;
		}
		return gcd;
	}
	
	
	
	public static Expr[] polynomial_extended_gcd(Expr[] u, Expr x)
	{
		if(u.length == 1)
			return new Expr[]{u[0], Int.ONE};
		if(u.length == 2)
			//return polynomial_extended_gcd(u[0], u[1], x);
		    return null;
		Expr u_1 = u[0];
		Expr[] u_r = Set.rest(u);
		Expr[] gcd_u_r = polynomial_extended_gcd(u_r, x);
		//Expr[] bc = polynomial_extended_gcd(u_1, gcd_u_r[0], x);
		Expr[] ext = new Expr[u.length+1];
		//ext[0] = bc[0];
		//ext[1] = bc[1];
		for(int i = 2;i<ext.length;i++);
			//ext[i] = Algebra.expand(gcd_u_r[i-1].mul(bc[2]));
		return ext;
	}
	
	
	
	
	
	
	
	
	
	public static Expr multivariate_euclid_gcd(Expr u, Expr v, Expr[] L, String K)
	{
		if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
			return Int.ZERO;
		if(u.equals(Int.ZERO))
			return normalize_gcd(v, L, K);
		if(v.equals(Int.ZERO))
			return normalize_gcd(u, L, K);
		return normalize_gcd(mv_euclid_rec(u, v, L, K), L, K);
	}

	private static Expr mv_euclid_rec(Expr u, Expr v, Expr[] L, String K)
	{
		if(L.length == 0)
		{
			if(K.equals("Z"))
			{
				return Int.gcd((Int) u, (Int) v);
			}
			else
			{
				return Int.ONE;
			}
		}
		else
		{
		    Expr x = L[0];
		    Expr[] R = Set.rest(L);
		    Expr cont_u = content(u, x, R, K, Constant.EUCLID);
		    Expr cont_v = content(v, x, R, K, Constant.EUCLID);
		    Expr d = mv_euclid_rec(cont_u, cont_v, R, K);
		    Expr pp_u = BasicPoly.multivariate_division(u, cont_u, L, K)[0];
		    Expr pp_v = BasicPoly.multivariate_division(v, cont_v, L, K)[0];
		    while(!pp_v.equals(Int.ZERO))
		    {
		    	Expr r = BasicPoly.pseudo_division(pp_u, pp_v, x)[1];
		    	Expr pp_r;
		    	if(r.equals(Int.ZERO))
		    		pp_r = Int.ZERO;
		    	else
		    	{
		    		Expr cont_r = content(r, x, R, K, Constant.EUCLID);
		    		pp_r = BasicPoly.multivariate_division(r, cont_r, L, K)[0];
		    	}
		    	pp_u = pp_v;
		    	pp_v = pp_r;
		    }
		    return Algebra.expand(d.mul(pp_u));
		}
	}

	private static Expr normalize_gcd(Expr u, Expr[] L, String K)
	{
		if(K.equals("Z"))
		{
			Int lcu = (Int) Poly.leading_coef(u, L);
			if(lcu.isNegative())
				return Algebra.expand(Int.NONE.mul(u));
			return u;
		}
		else
		{
			Numerical lcu = (Numerical) Poly.leading_coef(u, L);
			return Algebra.expand(u.div(lcu));
		}
	}
	
	public static Expr multivariate_gcd_sr(Expr u, Expr v, Expr[] L, String K)
	{
		if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
			return Int.ZERO;
		if(u.equals(Int.ZERO))
			return normalize_gcd(v, L, K);
		if(v.equals(Int.ZERO))
			return normalize_gcd(u, L, K);
		return normalize_gcd(mv_subresultant_rec(u, v, L, K), L, K);
	}

	private static Expr mv_subresultant_rec(Expr u, Expr v, Expr[] L, String K)
	{
		if(L.length == 0)
		{
			if(K.equals("Z"))
				return Int.gcd((Int)u, (Int) v);
			else
				return Int.ONE;
		}
		else
		{
			Expr x = L[0];
			Expr U, V;
			if(Poly.degree(u, x).compareTo(Poly.degree(v, x)) >= 0)
			{
				U = u;
				V = v;
			}
			else
			{
				U = v;
				V = u;
			}
			Expr[] R = Set.rest(L);
			Expr cont_U = content(U, x, R, K, Constant.SUBRESULTANT);
			Expr cont_V = content(V, x, R, K, Constant.SUBRESULTANT);
			Expr d =  multivariate_gcd_sr(cont_U, cont_V, R, K);
			U = BasicPoly.multivariate_division(U, cont_U, L, K)[0];
			V = BasicPoly.multivariate_division(V, cont_V, L, K)[0];
			Expr g = multivariate_gcd_sr(Poly.leading_coef(U, x), Poly.leading_coef(V, x), R, K);
			Int i = Int.ONE;
			Int delta = Int.ZERO;
			Expr beta = Int.ZERO;
			Expr psi = Int.ZERO;
			while(!V.equals(Int.ZERO))
			{
				Expr r = BasicPoly.pseudo_division(U, V, x)[1];
				if(!r.equals(Int.ZERO))
				{
					if(i.equals(Int.ONE))
					{
						delta = Poly.degree(U, x).sub(Poly.degree(V, x)).add(Int.ONE);
						psi = Int.NONE;
						beta = Int.NONE.pow(delta);
					}
					else if(i.compareTo(Int.ONE) > 0)
					{
						Int delta_p = delta;
						delta = Poly.degree(U, x).sub(Poly.degree(V, x)).add(Int.ONE);
						Expr f = Poly.leading_coef(U, x);
						Expr t_1 = Algebra.expand(Int.NONE.mul(f).pow(delta_p.sub(Int.ONE)));
						Expr t_2 = Algebra.expand(psi.pow(delta_p.sub(Int.TWO)));
					    psi = BasicPoly.multivariate_division(t_1, t_2, L, K)[0];
					    beta = Algebra.expand(Int.NONE.mul(f).mul(psi.pow(delta.sub(Int.ONE))));
					}
					U = V;
					V = BasicPoly.multivariate_division(r, beta, L, K)[0];
					i = i.add(Int.ONE);
				}
				else
				{
					U = V;
					V = r;
				}
			}
			Expr s = BasicPoly.multivariate_division(Poly.leading_coef(U, x), g, R, K)[0];
			Expr W = BasicPoly.multivariate_division(U, s, L, K)[0];
			Expr cont_W = content(W, x, R, K, Constant.SUBRESULTANT);
			Expr pp_W = BasicPoly.multivariate_division(W, cont_W, L, K)[0];
			return Algebra.expand(d.mul(pp_W));
		}
	}
	
	public static Expr[] solve(Expr a, Expr b, Expr c, Expr x)
	{
	    /*
		Expr[] gst = polynomial_extended_gcd(a, b, x);
		Expr s = gst[1], t = gst[2], g = gst[0];
		Expr[] qr = BasicPoly.polynomial_division(c, g, x);
		Expr q = qr[0], r = qr[1];
		if(!r.equals(Int.ZERO))
			return null;
		s = Algebra.expand(q.mul(s));
		t = Algebra.expand(q.mul(t));
		if(!s.equals(Int.ZERO) && Poly.degree(s, x).compareTo(Poly.degree(b, x)) >= 0)
		{
			qr = BasicPoly.polynomial_division(s, b, x);
			q = qr[0]; r = qr[1];
			s = r; t = Algebra.expand(t.add(q.mul(a)));
		}
		return new Expr[]{s, t};
		*/
	    return null;
	}
	
	public static Constant gcd_method(Expr u, Expr v, Expr[] L)
	{
		if(L.length > 3)
			return Constant.SUBRESULTANT;
		return Constant.MODULAR;
	}

	public static Expr polynomial_gcd(Expr u, Expr v, Expr x, Expr[] p, Expr[] a)
	{
		if(p.length == 0)
			return GCD.polynomial_gcd(u, v, x);
		u = AlgebraicNumberField.simplify_coef(u, x, p, a);
		v = AlgebraicNumberField.simplify_coef(v, x, p, a);
		if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
			return Int.ZERO;
		Expr U = u;
		Expr V = v;
		while(!V.equals(Int.ZERO))
		{
			Expr R = AlgebraicNumberField.polynomial_remainder(U, V, x, p, a);
			U = V;
			V = R;
		}
		return AlgebraicNumberField.make_monic(U, x, p, a);
	}

	public static Expr[] polynomial_extended_gcd(Expr u, Expr v, Expr x, Expr[] p, Expr[] a)
	{
		if(p.length == 0)
			return GCD.polynomial_extended_gcd(u, v, x);
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
			Expr[] qr = AlgebraicNumberField.polynomial_division(U, V, x, p, a);
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
		Expr c_i = AlgebraicNumberField.inverse(c, p, a);
		App = AlgebraicNumberField.simplify_coef(App.mul(c_i), x, p, a);
		Bpp = AlgebraicNumberField.simplify_coef(Bpp.mul(c_i), x, p, a);
		U = AlgebraicNumberField.simplify_coef(U.div(c), x, p, a);
		return new Expr[]{U, App, Bpp};
	}
}


