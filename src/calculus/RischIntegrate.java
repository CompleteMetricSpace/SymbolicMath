package calculus;

import algebra.Algebra;
import algebra.FunctionTransforms;
import polynomial.Cancel;
import polynomial.Factor;
import polynomial.GCD;
import polynomial.GCDAlgebraicNumberField;
import polynomial.Poly;
import polynomial.Resultant;
import solve.PolySolve;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.*;

public class RischIntegrate 
{
	
	public static Expr normal(Expr u, Expr x)
	{
		if(u.isSymbolic() || u.isFreeOf(x))
			return u;
		Expr[] v = new Expr[u.length()];
		for(int i = 0;i<u.length();i++)
			v[i] = normal(u.get(i), x);
		Expr U = Simplification.simplify_recursive(new Expr(u.getOperator(), v));
		if(!U.equals(u))
			return normal(U, x);
		if(U.getOperator().equals(Operator.EXP))
		{
			Expr A = Algebra.cancel(U.get(0));
			if(!A.isSum())
				A = new Expr(Operator.ADD, A);
			Expr s = Int.ONE;
			for(int i = 0;i<A.length();i++)
			{
				Expr[] ct = Simplification.constant_term(A.get(i));
				if(ct[0].isInt())
				    s = s.mul(ct[1].exp().pow(ct[0]));
				else
					s = s.mul(A.get(i).exp());
			}
			return s;
		}
		if(U.getOperator().equals(Operator.LOG))
		{
			Expr A = Algebra.cancel(U.get(0));
			Expr[] nd = Algebra.NumeratorDenominator(A);
			Expr[] vars = Set.union(Poly.variables(nd[0]), Poly.variables(nd[1]));
			Int lcm_n = Poly.coefficient_lcm(nd[0], vars);
			Int lcm_d = Poly.coefficient_lcm(nd[1], vars);
			nd[0] = nd[0].mul(lcm_n.mul(lcm_d));
			nd[1] = nd[1].mul(lcm_d.mul(lcm_n));
			Int c_n = GCD.integer_content(nd[0], vars);
			Int c_d = GCD.integer_content(nd[1], vars);
			Expr n = nd[0].div(c_n);
			Expr d = nd[1].div(c_d);
			Expr[][] f_n = Factor.factor_poly_rationals(n);
			Expr[][] f_d = Factor.factor_poly_rationals(d);
			Expr r = Int.ZERO;
			for(int i = 0;i<f_n.length;i++)
			    for(int j = 0;j<f_n[i].length;j++)
			    	r = r.add(new Int(i+1).mul(f_n[i][j].log()));
			r = r.add(c_n.log());
			for(int i = 0;i<f_d.length;i++)
			    for(int j = 0;j<f_d[i].length;j++)
			    	r = r.sub(new Int(i+1).mul(f_d[i][j].log()));
			r = r.sub(c_d.log());
			return r;
		}
		if(U.isPower() && !U.get(1).isFreeOf(x))
			return normal(U.get(1).mul(U.get(0).log()).exp(), x);
		return Algebra.cancel(U);
	}
	
	public static boolean is_exp_log_function(Expr u, Expr x)
	{
		if(u.isSymbolic() || u.isFreeOf(x))
			return true;
		if(u.equals(x))
			return true;
		boolean f = true;
		for(int i = 0;i<u.length();i++)
			if(!is_exp_log_function(u.get(i), x))
				f = false;
		if(!f)
			return false;
		if(u.getOperator().equals(Operator.LOG))
			return true;
		if(u.getOperator().equals(Operator.EXP))
			return true;
		if(u.isSum())
			return true;
		if(u.isProduct())
			return true;
		if(u.isPower() && u.get(1).isInt())
			return true;
		return false;
	}
	
    public static Expr[] find_extensions(Expr u, Expr x)
    {
    	if(u.equals(x))
    		return new Expr[]{x};
        if(u.isSymbolic())
        	return new Expr[]{};
        if(u.isFreeOf(x))
        	return new Expr[]{};
        Expr[] l = new Expr[]{};
        for(int i = 0;i<u.length();i++)
        	l = Set.union(l, find_extensions(u.get(i), x));
        if(u.getOperator().equals(Operator.EXP))
    		l = Set.union(l, new Expr[]{u});
    	if(u.getOperator().equals(Operator.LOG))
    		l = Set.union(l, new Expr[]{u});
    	return l;
    }
    
    public static Expr[][] get_diff_extensions(Expr u, Expr[] ext, Expr x)
    {
    	DExtension[] t = new DExtension[ext.length];
    	Expr[] v = Simplification.getNewVariables(ext.length, u);
    	for(int i = 0;i<t.length;i++)
    	{
    		if(ext[i].equals(x))
    		{
    			t[i] = new DExtension(((Var)v[i]).getName(), "X", x);
    		}
    		if(ext[i].getOperator().equals(Operator.LOG))
    		{
    			t[i] = new DExtension(((Var)v[i]).getName(), "LOG", ext[i].get(0));
    		}
    		if(ext[i].getOperator().equals(Operator.EXP))
    		{
    			t[i] = new DExtension(((Var)v[i]).getName(), "EXP", ext[i].get(0));
    		}
    		for(int j = i+1;j<ext.length;j++)
    		{
    			ext[j] = ext[j].substitute(ext[i], t[i]);
    		}
    		u = u.substitute(ext[i], t[i]);
    	}
    	return new Expr[][]{{u}, t};
    }
    
    public static Expr dextension_to_expr(Expr u, DExtension[] ext)
    {
    	for(int i = ext.length-1;i >= 0;i--)
    	{
    		DExtension t = ext[i];
    		if(t.isExp())
    			u = Simplification.simplify_recursive(u.substitute(t, t.getArg().exp()));
    		if(t.isLog())
    			u = Simplification.simplify_recursive(u.substitute(t, t.getArg().log()));
    		if(t.isX())
    			u = Simplification.simplify_recursive(u.substitute(t, t.getArg()));
    	}
    	return Simplification.simplify_recursive(u);
    }
    
    public static Expr expr_to_dextension(Expr u, DExtension[] ext)
    {
    	for(int i = 0;i<ext.length;i++)
    	{
    		DExtension t = ext[i];
    		if(t.isExp())
    			u = Simplification.simplify_recursive(u.substitute(t.getArg().exp(), t));
    		if(t.isLog())
    			u = Simplification.simplify_recursive(u.substitute(t.getArg().log(), t));
    		if(t.isX())
    			u = Simplification.simplify_recursive(u.substitute(t.getArg(), t));
    	}
    	return Simplification.simplify_recursive(u);
    }
    
    public static Expr risch_substitution(Expr u, DExtension[] ext, Expr x)
    {
    	u = normal(u, x);
    	return Algebra.cancel(expr_to_dextension(u, ext));
    }
    
    public static Expr integrate_risch(Expr u, Expr x)
    {
    	Expr[] ext = find_extensions(u, x);
    	Expr[][] dext = get_diff_extensions(u, ext, x);
    	Expr integrand = dext[0][0];
    	DExtension[] extensions = new DExtension[ext.length];
    	for(int i = 0;i<extensions.length;i++)
    	    extensions[i] = (DExtension)dext[1][i];
    	Expr integral = integrate_risch(integrand, extensions);
    	if(integral == null)
    		return null;
    	else
    	{
    		for(int i = extensions.length-1;i>=0;i--)
    		{
    			Expr subs = null;
    			DExtension t = extensions[i];
    			if(t.getType().equals("X"))
    				subs = t.getArg();
    			if(t.getType().equals("LOG"))
    				subs = new Expr(Operator.LOG, t.getArg());
    			if(t.getType().equals("EXP"))
    				subs = new Expr(Operator.EXP, t.getArg());
    			integral = integral.substitute(t, subs);
    		}
    		return Simplification.simplify_recursive(integral);
    	}
    }
    
	public static Expr integrate_risch(Expr u, DExtension[] ext)
	{
		u = Algebra.cancel(u);
		Expr[] nd = Algebra.NumeratorDenominator(u);
		Expr[][] integral = integrate_risch_rec(nd[0], nd[1], ext);
		if(integral == null)
			return null;
		return integral_to_expr(integral);
	}
	
	private static Expr integral_to_expr(Expr[][] integral) 
	{
		Expr e = integral[0][0];
		for(int i = 1;i<integral.length;i++)
			e = e.add(integral[i][0].mul(new Expr(Operator.LOG, integral[i][1])));
		return e;
	}

	/**
	 * Recursive procedure for integrating transcendental elementary functions
	 * @param p - a multivariate polynomial in Q[ext]
	 * @param q - a multivariate polynomial in Q[ext]
	 * @param ext - a list of differential extensions [t1, ..., tn]
	 * @return the list [[v_0], [c_1, v_1], ..., [c_k, v_k]] such that <br>
	 *         integral p/q = v_0 + c_1 log(v_1) + ... + c_k log(v_k) <br>
	 *         or null if there doesn't exist any elementary integral
 	 */
	public static Expr[][] integrate_risch_rec(Expr p, Expr q, DExtension[] ext)
	{
		DExtension t = (DExtension) Set.last(ext);
		if(t.isX())
			return RationalIntegrate.integrate_rational_function_list(p, q, t);
		if(t.isLog())
			return integrate_log_extension(p, q, ext);
		if(t.isExp())
			return integrate_exp_extension(p, q, ext);
		throw new IllegalArgumentException("Extension not supported: "+t);
	}
	
	public static Expr[][] integrate_risch_rec(Expr u, DExtension[] ext)
	{
		u = Algebra.cancel(u);
		Expr[] nd = Algebra.NumeratorDenominator(u);
		Expr[][] integral = integrate_risch_rec(nd[0], nd[1], ext);
		if(integral == null)
			return null;
		return integral;
	}

	private static Expr[][] integrate_log_extension(Expr p, Expr q, DExtension[] ext) 
	{
		DExtension t = (DExtension) Set.last(ext);
		//Make q monic 
		Expr lc_q = Poly.leading_coef(q, t);
		q = Cancel.multiply(q, Int.ONE.div(lc_q), t);
		p = Cancel.multiply(p, Int.ONE.div(lc_q), t);
		Expr[] QR = Cancel.polynomial_division_cancel(p, q, t);
		Expr s = QR[0];
		Expr r = QR[1];
		Expr[][] rational = integrate_log_rational_part(r, q, ext);
		if(rational == null)
			return null;
		Expr[][] poly = integrate_log_poly_part(s, ext);
		if(poly == null)
			return null;
		Expr[][] integral = new Expr[][]{{rational[0][0].add(poly[0][0])}};
		for(int i = 1;i<rational.length;i++)
			integral = Set.add(integral, new Expr[][]{rational[i]});
		for(int i = 1;i<poly.length;i++)
			integral = Set.add(integral, new Expr[][]{poly[i]});
		return integral;
	}

	public static Expr[][] integrate_log_poly_part(Expr s, DExtension[] ext) 
	{
		if(s.equals(Int.ZERO))
			return new Expr[][]{{Int.ZERO}};
		DExtension t = (DExtension) Set.last(ext);
		DExtension x = ext[0];
	    DExtension[] rest = new DExtension[ext.length-1];
	    for(int i = 0;i<rest.length;i++)
	    	rest[i] = ext[i];
		Int n = Poly.degree(s, t);
		Expr[] a = new Expr[n.toInt()+2];
		Expr[] b = new Expr[n.toInt()+1];
		Expr[][] mhy_zero = null;
		a[n.toInt()+1] = Int.ZERO;
		Expr D = Diff.derivative(t, x);
		for(Int i = n;i.compareTo(Int.ZERO)>=0;i = i.sub(Int.ONE))
		{
			Expr lambda = Poly.coefficient_poly(s, t, i);
			Expr integrand = Algebra.cancel(lambda.sub(i.add(Int.ONE).mul(a[i.toInt()+1].mul(D))));
			Expr[] nd = Algebra.NumeratorDenominator(integrand);
			Expr[][] I = integrate_risch_rec(nd[0], nd[1], rest);
			if(I == null)
				return null;
			if(i.compareTo(Int.ZERO) > 0)
			{
				if(I.length >= 2)
				{
					if(!lies_in_log_extension(I, D, x))
						return null;
					b[i.toInt()] = Int.ZERO;
					for(int j = 1;j<I.length;j++)
					    b[i.toInt()] = b[i.toInt()].add(I[j][0]);
					a[i.toInt()] = I[0][0];
				}
				else
				{
					b[i.toInt()] = Int.ZERO;
					a[i.toInt()] = I[0][0];
				}
			}
			else
			{
				b[0] = Int.ZERO;
				mhy_zero = new Expr[][]{{I[0][0]}};
				for(int j = 1;j<I.length;j++)
				{
					Expr diff = Algebra.cancel(D.sub(Diff.derivative(I[j][1], x).div(I[j][1])));
					if(diff.equals(Int.ZERO))
					{
						b[0] = b[0].add(I[j][0]);
					}
					else
					{
						mhy_zero = Set.add(mhy_zero, new Expr[][]{I[j]});
					}
				}
			}	
		}
		for(Int i = Int.ONE;i.compareTo(n.add(Int.ONE)) <= 0;i = i.add(Int.ONE))
		{
			Expr mhy = a[i.toInt()].add(b[i.toInt()-1].div(i));
			mhy_zero[0][0] = mhy_zero[0][0].add(mhy.mul(t.pow(i)));
		}
		return mhy_zero;
	}

	private static Expr[][] integrate_log_rational_part(Expr r, Expr q, DExtension[] ext)
	{
		DExtension t = (DExtension) Set.last(ext);
		DExtension x = ext[0];
		Expr[] h = hermite_reduction(r, q, ext);
		if(h[1].equals(Int.ZERO))
			return new Expr[][]{{h[0]}};
		Expr a = h[1];
		Expr b = h[2];
		Expr b_prime = Diff.derivative(b, x);
		Expr z = Simplification.getNewVariables(1, a, b, b_prime)[0];
		Expr W = Cancel.subtract(a, Cancel.multiply(z, b_prime, t), t);
		Expr R = Resultant.multivariate_resultant(W, b, t, "Q");
		R = Algebra.NumeratorDenominator(Algebra.cancel(R))[0];
		R = GCD.primitive(R, z);
		Int n = Poly.degree(R, z);
		for(Int i = Int.ZERO;i.compareTo(n) <= 0;i = i.add(Int.ONE))
			if(!Poly.coefficient_poly(R, z, i).isFreeOf(ext))
				return null;
		Expr[] factors = Factor.factor_poly_rationals_distinct(R);
		Expr[][] logs = new Expr[][]{};
		for(int i = 0;i<factors.length;i++)
		{
			Int d = Poly.degree(factors[i], z);
			if(d.equals(Int.ZERO))
				continue;
			if(d.equals(Int.ONE))
			{
				Expr c = PolySolve.solve_polynomial(factors[i], z)[0];
				Expr w = Simplification.simplify_recursive(W.substitute(z, c));
				Expr v = Cancel.polynomial_gcd_cancel(w, b, t);
				logs = Set.add(logs, new Expr[][]{{c, v}});
			}
			else
			{
				Expr[] c = PolySolve.solve_polynomial(factors[i], z);
				Expr v = GCDAlgebraicNumberField.polynomial_gcd(W, b, t, new Expr[]{factors[i]}, new Expr[]{z});
				for(int j = 0;j<c.length;j++)
				{
					logs = Set.add(logs, new Expr[][]{{c[j], Simplification.simplify_recursive(v.substitute(z, c[j]))}});
				}
			}
				
		}
		return Set.add(new Expr[][]{{h[0]}}, logs);
	}
	
	public static Expr[] hermite_reduction(Expr p, Expr q, DExtension[] ext)
	{
		DExtension t = (DExtension) Set.last(ext);
		DExtension x = ext[0];
		Expr g = Int.ZERO;
		Expr[] D = Cancel.square_free_factorization_cancel(q, t);
		int m = D.length;
		for(int i = 2;i <= m;i++)
		{
			if(Poly.degree(D[i-1], t).compareTo(Int.ZERO) > 0)
			{
				Expr V = D[i-1];
				Expr U = Cancel.polynomial_division_cancel(q, Algebra.expand(V.pow(new Int(i))), t)[0];
				for(int j = i-1;j>=1;j--)
				{
					Expr w = Cancel.multiply(U, Diff.derivative(V, x), t);
					Expr r = p.div(new Int(-j));
					Expr[] BC = Cancel.solve_cancel(w, V, r, t);
					Expr B = BC[0], C = BC[1];
					g = Algebra.cancel(g.add(B.div(V.pow(new Int(j)))));
					p = Cancel.subtract(new Int(-j).mul(C), Cancel.multiply(U, Diff.derivative(B, x), t), t);
				}
				q = Cancel.multiply(U, V, t);
			}
		}
		Expr k = Algebra.cancel(p.div(q));
		Expr[] pq = Algebra.NumeratorDenominator(k);
		return new Expr[]{g, pq[0], pq[1]};
	}
	
	public static boolean lies_in_log_extension(Expr[][] I, Expr D, Expr x)
	{
		if(I.length <= 1)
			return true;
		for(int i = 1;i<I.length;i++)
		{
			Expr diff = Algebra.cancel(D.sub(Diff.derivative(I[i][1], x).div(I[i][1])));
			if(!diff.equals(Int.ZERO))
				return false;
		}
		return true;
	}
	
	private static Expr[][] integrate_exp_extension(Expr p, Expr q, DExtension[] ext) 
	{
		DExtension t = (DExtension) Set.last(ext);
		Expr[] QR = Cancel.polynomial_division_cancel(p, q, t);
		Expr s = QR[0];
		Expr r = QR[1];
		Int l = Poly.min_degree(q, t);
		Expr q_ = Cancel.polynomial_division_cancel(q, t.pow(l), t)[0];
		Expr[] r_w = Cancel.solve_cancel(t.pow(l), q_, r, t);
		Expr r_ = r_w[0];
		Expr w = r_w[1];
		Expr s_ = s.add(Cancel.simplify_gie(w.div(t.pow(l)), t));
		Expr[][] rational = integrate_exp_rational_part(r_, q_, ext);
		if(rational == null)
			return null;
		Expr[][] poly = integrate_exp_poly_part(s_, ext);
		if(poly == null)
			return null;
		Expr[][] integral = new Expr[][]{{rational[0][0].add(poly[0][0])}};
		for(int i = 1;i<rational.length;i++)
			integral = Set.add(integral, new Expr[][]{rational[i]});
		for(int i = 1;i<poly.length;i++)
			integral = Set.add(integral, new Expr[][]{poly[i]});
		return integral;
	}

	private static Expr[][] integrate_exp_rational_part(Expr r, Expr q, DExtension[] ext)
	{
		DExtension t = (DExtension) Set.last(ext);
		Expr u = t.getArg();
		DExtension x = ext[0];
		Expr[] h = hermite_reduction(r, q, ext);
		if(h[1].equals(Int.ZERO))
			return new Expr[][]{{h[0]}};
		Expr a = h[1];
		Expr b = h[2];
		Expr b_prime = Diff.derivative(b, x);
		Expr z = Simplification.getNewVariables(1, a, b, b_prime)[0];
		Expr W = Cancel.simplify(a.sub(z.mul(b_prime)), t);
		Expr R = Resultant.multivariate_resultant(W, b, t, "Q");
		R = Algebra.NumeratorDenominator(Algebra.cancel(R))[0];
		R = GCD.primitive(R, z);
		Int n = Poly.degree(R, z);
		for(Int i = Int.ZERO;i.compareTo(n) <= 0;i = i.add(Int.ONE))
			if(!Poly.coefficient_poly(R, z, i).isFreeOf(ext))
				return null;
		Expr[] factors = Factor.factor_poly_rationals_distinct(R);
		Expr[][] logs = new Expr[][]{};
		Expr sum = Int.ZERO;
		for(int i = 0;i<factors.length;i++)
		{
			Int d = Poly.degree(factors[i], z);
			if(d.equals(Int.ZERO))
				continue;
			if(d.equals(Int.ONE))
			{
				Expr c = PolySolve.solve_polynomial(factors[i], z)[0];
				Expr w = Simplification.simplify_recursive(W.substitute(z, c));
				Expr v = Cancel.polynomial_gcd_cancel(w, b, t);
				logs = Set.add(logs, new Expr[][]{{c, v}});
				sum = sum.add(Poly.degree(v, t).mul(c));
			}
			else
			{
				Expr[] c = PolySolve.solve_polynomial(factors[i], z);
				Expr v = GCDAlgebraicNumberField.polynomial_gcd(W, b, t, new Expr[]{factors[i]}, new Expr[]{z});
				for(int j = 0;j<c.length;j++)
				{
					logs = Set.add(logs, new Expr[][]{{c[j], Simplification.simplify_recursive(v.substitute(z, c[j]))}});
					sum = sum.add(Poly.degree(v, t).mul(c[j]));
				}
			}
				
		}
		return Set.add(new Expr[][]{{h[0].sub(sum.mul(u))}}, logs);
	}
	
	private static Expr[][] integrate_exp_poly_part(Expr s, DExtension[] ext)
	{
	    if(s.equals(Int.ZERO))
	    	return new Expr[][]{{Int.ZERO}};
	    DExtension t = (DExtension) Set.last(ext);
	    Expr x = ext[0];
		Expr u = t.getArg();
		Expr u_p = Diff.derivative(u, x);
		DExtension[] rest = new DExtension[ext.length-1];
	    for(int i = 0;i<rest.length;i++)
	    	rest[i] = ext[i];
	    Int k = Poly.min_degree_gie(s, t);
	    Int l = Poly.degree_gie(s, t);
	    Expr p_0 = Poly.coefficient_poly_gie(s, t, Int.ZERO);
	    Expr[] nd = Algebra.NumeratorDenominator(p_0);
	    Expr[][] q_0 = integrate_risch_rec(nd[0], nd[1], rest);
	    if(q_0 == null)
            return null;
	    for(Int j = k;j.compareTo(Int.NONE) <= 0;j = j.add(Int.ONE))
	    {
	        Expr f = j.mul(u_p);
	        Expr g = Poly.coefficient_poly_gie(s, t, j);
	        Expr y = solve_risch_de(f, g, rest);
	        if(y == null)
	        	return null;
	        q_0[0][0] = Algebra.cancel(q_0[0][0].add(y.mul(t.pow(j))));
	    }
	    for(Int j = Int.ONE;j.compareTo(l) <= 0;j = j.add(Int.ONE))
	    {
	        Expr f = j.mul(u_p);
	        Expr g = Poly.coefficient_poly_gie(s, t, j);
	        Expr y = solve_risch_de(f, g, rest);
	        if(y == null)
	        	return null;
	        q_0[0][0] = Algebra.cancel(q_0[0][0].add(y.mul(t.pow(j))));
	    }
	    return q_0;
	}
	
	public static Expr solve_risch_de(Expr f, Expr g, DExtension[] ext)
	{
		DExtension t = (DExtension) Set.last(ext);
	    Expr x = ext[0];
	    if(f.isFreeOf(ext) && g.isFreeOf(ext) && !f.equals(Int.ZERO))
	    	return g.div(f);
	    Expr[] AD = get_canonical_rep(f, t);
		Expr[] BE = get_canonical_rep(g, t);
		Expr G = Cancel.polynomial_gcd_cancel(AD[1], BE[1], t);
		Expr R_1 = Cancel.polynomial_gcd_cancel(BE[1], Diff.derivative(BE[1], t), t);
		Expr R_2 = Cancel.polynomial_gcd_cancel(G, Diff.derivative(G, t), t);
		Expr T = Cancel.polynomial_division_cancel(R_1, R_2, t)[0];
		Expr[] d = Cancel.polynomial_division_cancel(Cancel.simplify(AD[1].mul(T.pow(Int.TWO)), t), BE[1], t);
		if(!d[1].equals(Int.ZERO))
			return null;
		Expr c = Cancel.simplify_gie(BE[0].mul(d[0]), t);
		Expr b = Cancel.simplify_gie(AD[0].mul(T).sub(AD[1].mul(Diff.derivative(T, x))), t);
		Expr a = Cancel.simplify(AD[1].mul(T), t);
		Expr Q = solve_poly_de(a, b, c, ext);
		if(Q == null)
			return null;
		return Q.div(T);
	}
	 
	public static Expr[] get_canonical_rep(Expr u, DExtension t)
	{
		Expr[] nd = Algebra.NumeratorDenominator(Algebra.cancel(u));
		if(t.isX() || t.isLog())
		{
			Expr lc = Poly.leading_coef(nd[1], t);
			Expr Q = Cancel.simplify(nd[1].div(lc), t);
			Expr P = Cancel.simplify(nd[0].div(lc), t);
			return new Expr[]{P, Q};
		}
		if(t.isExp())
		{
			Expr lc = Poly.leading_coef(nd[1], t);
			Expr Q = Cancel.simplify(nd[1].div(lc), t);
			Expr P = Cancel.simplify(nd[0].div(lc), t);
			Int n = Poly.min_degree(Q, t);
			Expr Q_ = Cancel.simplify_gie(Q.div(t.pow(n)), t);
			Expr P_ = Cancel.simplify_gie(P.div(t.pow(n)), t);
			return new Expr[]{P_, Q_};
		}
		throw new IllegalArgumentException("Extension not supported: "+t);
	}
	
	public static Expr solve_poly_de(Expr A, Expr B, Expr C, DExtension[] ext)
	{
		if(ext.length == 1 && ext[0].isX())
            return poly_DE_base(A, B, C, ext);
		DExtension t = ext[ext.length-1];
		if(t.isLog())
			return poly_DE_primitive(A, B, C, ext);
		if(t.isExp())
		    return poly_DE_exponential(A, B, C, ext);	
		throw new IllegalArgumentException("Extension not supported: "+t);
	}

	private static Expr poly_DE_base(Expr A, Expr B, Expr C, DExtension[] ext) 
	{
		DExtension t = ext[ext.length-1];
		Int deg_A = Poly.degree(A, t);
		Int deg_B = Poly.degree(B, t);
		Int deg_C = Poly.degree(C, t);
		Int n = null;
		if(deg_A.compareTo(deg_B.add(Int.ONE)) < 0)
			n = deg_C.sub(deg_B);
		if(deg_A.compareTo(deg_B.add(Int.ONE)) > 0)
			n = Int.max(Int.ZERO, deg_C.sub(deg_A).add(Int.ONE));
		if(deg_A.compareTo(deg_B.add(Int.ONE)) == 0)
		{
			Expr a = Poly.leading_coef(A, t);
			Expr b = Poly.leading_coef(B, t);
			Expr r = Algebra.cancel(Int.NONE.mul(b).div(a));
			if(r.isInt())
				n = Int.max((Int)r, deg_C.sub(deg_B));
			else
				n = deg_C.sub(deg_B);
		}
		return spde(A, B, C, n, ext, "BASE");
	}
	
	public static Expr poly_DE_primitive(Expr A, Expr B, Expr C, DExtension[] ext)
	{
		DExtension t = ext[ext.length-1];
		DExtension x = ext[0];
		DExtension[] rest = new DExtension[ext.length-1];
	    for(int i = 0;i<rest.length;i++)
	    	rest[i] = ext[i];
		Int deg_A = Poly.degree(A, t);
		Int deg_B = Poly.degree(B, t);
		Int deg_C = Poly.degree(C, t);
		Int n = null;
		if(deg_A.equals(deg_B) && !deg_A.equals(Int.ZERO))
		{
			Expr a = Poly.leading_coef(A, t);
			Expr b = Poly.leading_coef(B, t);
			//TODO: Implement member detector
			Expr[][] I = integrate_risch_rec(Int.NONE.mul(b.div(a)), rest);
			if(I != null)
			{
				Expr alpha = dextension_to_expr(integral_to_expr(I), ext).exp();
				alpha = risch_substitution(alpha, ext, x.getArg());
				if(Poly.is_rational_f(alpha, rest) && alpha.isFreeOf(t))
				{
					Expr A_ = Cancel.simplify(alpha.mul(A), t);
					Expr B_ = Cancel.simplify(Diff.derivative(alpha, x).mul(A).add(alpha.mul(B)), t);
					Expr H = poly_DE_primitive(A_, B_, C, ext);
					if(H == null)
						return null;
					return Cancel.simplify(alpha.mul(H), t);
				}
				else
				{
					n = deg_C.sub(deg_B);
				}
			}
			else
			{
				n = deg_C.sub(deg_B);
			}
		}
		if(deg_A.compareTo(deg_B) < 0)
			n = deg_C.sub(deg_B);
		if(deg_A.compareTo(deg_B.add(Int.ONE)) > 0)
			n = Int.max(Int.ZERO, deg_C.sub(deg_A).add(Int.ONE));
		if(deg_A.compareTo(deg_B.add(Int.ONE)) == 0)
		{
			Expr a = Poly.leading_coef(A, t);
			Expr b = Poly.leading_coef(B, t);
		    //TODO: Implement member detector
			Expr[][] I = integrate_risch_rec(Int.NONE.mul(b).div(a), rest);
			if(I != null)
			{
				Expr s = dextension_to_expr(integral_to_expr(I), ext);
				s = risch_substitution(s, ext, x.getArg());
				if(Poly.is_poly(s, t))
				{
					Expr r = Poly.coefficient_poly(s, t, Int.ONE);
					if(r.isInt())
						n = Int.max((Int)r, deg_C.sub(deg_B));
					else
						n = deg_C.sub(deg_B);
				}
				else
					n = deg_C.sub(deg_B);
			}
			else
				n = deg_C.sub(deg_B);
		}
		System.out.println("A: "+A+" B: "+B+" C: " +C+" t: "+t+" targ: "+t.getArg());
		return spde(A, B, C, n, ext, "LOG");
	}
	
	public static Expr poly_DE_exponential(Expr A, Expr B, Expr C, DExtension[] ext)
	{
		System.out.println("polyDE exponential: A: "+A+" B: "+B+" C: "+C);
		DExtension t = ext[ext.length-1];
		DExtension x = ext[0];
		DExtension[] rest = new DExtension[ext.length-1];
	    for(int i = 0;i<rest.length;i++)
	    	rest[i] = ext[i];
	    Expr u = t.getArg();
	    Expr u_p = Diff.derivative(u, x);
	    Int n_B = Int.min(Int.ZERO, Poly.min_degree_gie(B, t));
	    Int n_C = Int.min(Int.ZERO, Poly.min_degree_gie(C, t));
	    Int b;
	    if(!n_B.equals(Int.ZERO))
	    	b = Int.min(Int.ZERO, n_C.sub(Int.min(Int.ZERO, n_B)));
	    else
	    {
	    	//TODO: Implement member detector
	    	Expr B_0 = Poly.coefficient_poly(B, t, Int.ZERO);
	    	Expr A_0 = Poly.coefficient_poly(A, t, Int.ZERO);
	    	Expr[][] I = integrate_risch_rec(B_0.div(A_0).mul(Int.NONE), rest);
	    	if(I != null)
			{
				Expr alpha = dextension_to_expr(integral_to_expr(I), ext).exp();
				alpha = Cancel.simplify_gie(risch_substitution(alpha, ext, x.getArg()), t);
				System.out.println("alpha: "+alpha);
				if(Poly.is_monomial_gie(alpha, t))
				{
					Expr[] bn = Poly.coefficient_monomial_gie(alpha, t);
					b = Int.min(Int.ZERO, Int.min((Int)bn[1], n_C));
				}
				else
					b = Int.min(Int.ZERO, n_C);
			}
	    	else
				b = Int.min(Int.ZERO, n_C);
	    }
	    Int m = Int.max(Int.ZERO, Int.max(Int.NONE.mul(n_C), b.sub(n_C)));
	    B = Cancel.simplify_gie(b.mul(u_p).mul(A).add(B).mul(t.pow(m)), t);
	    A = Cancel.simplify_gie(A.mul(t.pow(m)), t);
	    C = Cancel.simplify_gie(C.mul(t.pow(m.sub(b))), t);
	    Int deg_A = Poly.degree(A, t);
		Int deg_B = Poly.degree(B, t);
		Int deg_C = Poly.degree(C, t);
		if(deg_A.compareTo(deg_B) < 0)
			m = deg_C.sub(deg_B);
		if(deg_A.compareTo(deg_B) > 0)
			m = Int.max(Int.ZERO, deg_C.sub(deg_A));
		if(deg_A.equals(deg_B))
		{
			Expr a_c = Poly.leading_coef(A, t);
			Expr b_c = Poly.leading_coef(B, t);
			//TODO: Implement member detector
			Expr[][] I = integrate_risch_rec(Int.NONE.mul(b_c.div(a_c)), rest);
	    	if(I != null)
			{
				Expr alpha = dextension_to_expr(integral_to_expr(I), ext).exp();
				alpha = Cancel.simplify_gie(risch_substitution(alpha, ext, x.getArg()), t);
				if(Poly.is_monomial_gie(alpha, t))
				{
					Expr[] bn = Poly.coefficient_monomial_gie(alpha, t);
					m = Int.max(Int.ZERO, Int.max((Int)bn[1], deg_C.sub(deg_B)));
				}
				else
					m = deg_C.sub(deg_B);
			}
	    	else
				m = deg_C.sub(deg_B);
		}
		Expr H = spde(A, B, C, m, ext, "EXP");
		System.out.println("b: "+b);
		if(H == null)
			return null;
		return Cancel.simplify_gie(H.mul(t.pow(b)), t);
	}

	private static Expr spde(Expr A_, Expr B_, Expr C_, Int n, DExtension[] ext, String pde_k) 
	{
		System.out.println("SPDE: A: "+A_+" B: "+B_+" C: "+C_+" n: "+n+" t: "+ext[ext.length-1]);
		DExtension t = ext[ext.length-1];
		Expr x = ext[0];
		DExtension[] rest = new DExtension[ext.length-1];
	    for(int i = 0;i<rest.length;i++)
	    	rest[i] = ext[i];
		if(C_.equals(Int.ZERO))
			return Int.ZERO;
		if(n.compareTo(Int.ZERO) < 0)
			return null;
		Expr G = Cancel.polynomial_gcd_cancel(A_, B_, t);
		Expr[] qr = Cancel.polynomial_division_cancel(C_, G, t);
		if(!qr[1].equals(Int.ZERO))
			return null;
		Expr A = Cancel.polynomial_division_cancel(A_, G, t)[0];
		Expr B = Cancel.polynomial_division_cancel(B_, G, t)[0];
		Expr C = qr[0];
		if(B.equals(Int.ZERO))
		{
			//TODO: Implement member detector
			Expr[][] I = integrate_risch_rec(C, ext);
			if(I.length == 1)
			{
			    Expr p = Algebra.expand(I[0][0]);
			    if(Poly.is_poly(p, t) && Poly.degree(p, t).compareTo(n) <= 0)
				    return Cancel.simplify(p, t);
			}
			return null;
		}
		if(Poly.degree(A, t).isPositive())
		{
			Expr[] ZR = Cancel.solve_cancel(A, B, C, t);
			System.out.println("ZR: "+Expr.toString(ZR));
			Expr Z = ZR[0], R = ZR[1];
			if(Poly.degree(R, t).compareTo(n) > 0)
			    return null;
			Expr H = spde(A, B.add(Diff.derivative(A, x)), Z.sub(Diff.derivative(R, x)), n.sub(Poly.degree(A, t)), ext, pde_k);
			if(H == null)
				return null;
			if(Poly.degree(H, t).compareTo(n) > 0)
				return null;
			return Cancel.simplify(A.mul(H).add(R), t);
		}
		if((Poly.degree(A, t).equals(Int.ZERO) && Poly.degree(B, t).isPositive()) 
				|| (t.equals(x) && Poly.degree(A, t).equals(Int.ZERO) && Poly.degree(B, t).equals(Int.ZERO)))
		{
			Int m = Poly.degree(C, t).sub(Poly.degree(B, t));
			if(m.compareTo(n)>0 || m.isNegative())
				return null;
			Expr b = Poly.leading_coef(B, t);
			Expr c = Poly.leading_coef(C, t);
			Expr Z = C.sub(c.div(b).mul(B).mul(t.pow(m))).sub(A.mul(Diff.derivative(c.div(b).mul(t.pow(m)), x)));
			Z = Cancel.simplify(Z, t);
			Expr H = spde(A, B, Z, m.sub(Int.ONE), ext, pde_k);
			if(H == null)
				return null;
			return c.div(b).mul(t.pow(m)).add(H);
		}
		return pde_k(A, B, C, n, ext, pde_k);
	}

	private static Expr pde_k(Expr A, Expr B, Expr C, Int n, DExtension[] ext, String pde_k)
	{
		System.out.println("pde_k: "+pde_k);
		if(pde_k.equals("EXP"))
			return pde_k_exponential(A, B, C, n, ext);
		if(pde_k.equals("LOG"))
			return pde_k_primitive(A, B, C, n, ext);
		return null;
	}

	private static Expr pde_k_primitive(Expr a, Expr b, Expr c, Int n, DExtension[] ext) 
	{
		return null;
	}

	private static Expr pde_k_exponential(Expr a, Expr b, Expr c, Int n, DExtension[] ext)
	{
		return null;
	}
	
	
	
}
