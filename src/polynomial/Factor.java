package polynomial;

import java.util.Vector;

import algebra.Algebra;
import algebra.AlgebraicNumberField;
import calculus.Diff;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;

public class Factor 
{
	public static Expr factor_poly_rationals_expr(Expr u)
	{
		if(u.equals(Int.ZERO))
			return Int.ZERO;
		Expr[][] f = factor_poly_rationals(u);
		Vector<Expr> M = new Vector<Expr>();
		for(int i = 0;i<f.length;i++)
		{
			for(int j = 0;j<f[i].length;j++)
			{
				M.add(f[i][j].pow(new Int(i+1)));
			}
		}
		return Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, M.toArray(new Expr[M.size()])));
	}
    
	public static Expr factor_poly_rationals_expr(Expr u, Expr x)
	{
		if(u.equals(Int.ZERO))
			return Int.ZERO;
		Expr[][] f = factor_poly_rationals(u, x);
		Vector<Expr> M = new Vector<Expr>();
		for(int i = 0;i<f.length;i++)
		{
			for(int j = 0;j<f[i].length;j++)
			{
				M.add(f[i][j].pow(new Int(i+1)));
			}
		}
		return Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, M.toArray(new Expr[M.size()])));
	}
	
	public static Expr factor_poly_p_expr(Expr u, Expr x, Int p)
	{
		if(u.equals(Int.ZERO))
			return Int.ZERO;
		Expr[][] f = factor_poly_p(u, x, p);
		Vector<Expr> M = new Vector<Expr>();
		for(int i = 0;i<f.length;i++)
		{
			for(int j = 0;j<f[i].length;j++)
			{
				M.add(f[i][j].pow(new Int(i+1)));
			}
		}
		return Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, M.toArray(new Expr[M.size()])));
	}
	
	public static Expr factor_poly_algebraic_number_field_expr(Expr u, Expr x, Expr p, Expr a)
	{
		if(u.equals(Int.ZERO))
			return Int.ZERO;
		Expr[][] f = factor_poly_algebraic_number_field(u, x, p, a);
		Vector<Expr> M = new Vector<Expr>();
		for(int i = 0;i<f.length;i++)
		{
			for(int j = 0;j<f[i].length;j++)
			{
				M.add(f[i][j].pow(new Int(i+1)));
			}
		}
		return Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, M.toArray(new Expr[M.size()])));
	}
	
	public static Expr[] factor_poly_rationals_one_list(Expr u, Expr x)
	{
	    Expr[][] f = factor_poly_rationals(u, x);
	    Vector<Expr> v = new Vector<Expr>();
	    for(int i = 0;i<f.length;i++)
	    {
	    	for(int j = 0;j<f[i].length;j++)
	    	{
	    		for(int k = 0;k<i+1;k++)
	    			v.add(f[i][j]);
	    	}
	    }
	    return v.toArray(new Expr[v.size()]);
	}
	
	public static Expr[] factor_poly_integers_one_list(Expr u, Expr x)
	{
	    Expr[][] f = factor_poly_integers(u, x);
	    Vector<Expr> v = new Vector<Expr>();
	    for(int i = 0;i<f.length;i++)
	    {
	    	for(int j = 0;j<f[i].length;j++)
	    	{
	    		for(int k = 0;k<i+1;k++)
	    			v.add(f[i][j]);
	    	}
	    }
	    return v.toArray(new Expr[v.size()]);
	}
	
	public static Expr[] factor_poly_rationals_distinct(Expr u)
	{
	    Expr[][] f = factor_poly_rationals(u);
	    Expr[] d = new Expr[]{};
	    for(int i = 0;i<f.length;i++)
	    {
	    	d = Set.union(d, f[i]);
	    }
	    return d;
	}
	
	public static Expr[] factor_poly_rationals_distinct(Expr u, Expr x)
	{
	    Expr[][] f = factor_poly_rationals(u, x);
	    Expr[] d = new Expr[]{};
	    for(int i = 0;i<f.length;i++)
	    {
	    	d = Set.union(d, f[i]);
	    }
	    return d;
	}
	
	/**
	 * Factors polynomial over Q
	 * @param u an expression
	 * @return the list [[u_1,...,u_k],[...],...,[v_1,...,v_l]] with u = (u_1...u_k)^1...(v_1...v_l)^n
	 */
	public static Expr[][] factor_poly_rationals(Expr u)
	{
		Expr[] vars = Poly.variables(u);
	    if(vars.length == 0)
	    	return new Expr[][]{{u}};
	    Expr[] subs = Simplification.getNewVariables(vars.length, u);
	    u = u.substitute(vars, subs);
	    Expr[][] factors = multivariate_factorization_rationals(u, subs);
	    Expr[][] factors_vars = new Expr[factors.length][];
	    for(int i = 0;i<factors.length;i++)
	    {
	    	factors_vars[i] = new Expr[factors[i].length];
	    	for(int j = 0;j<factors[i].length;j++)
	    		factors_vars[i][j] = Simplification.simplify_recursive(factors[i][j].substitute(subs, vars));
	    }
	    return factors_vars;
	}
	
	public static Expr[][] factor_poly_rationals(Expr u, Expr x)
	{
		if(u.equals(Int.ZERO))
			return new Expr[][]{{Int.ZERO}};
		Expr lcm = Poly.coefficient_lcm(u, new Expr[]{x});
		u = u.mul(lcm);
		Expr[][] factors = factor_poly_integers(u, x);
		if(lcm.equals(Int.ONE))
			return factors;
		factors[0] = Set.add(new Expr[]{Int.ONE.div(lcm)}, factors[0]);
		return factors;
	}
	
	public static Expr[][] factor_poly_integers(Expr u, Expr x)
	{
		if(u.equals(Int.ZERO))
			return new Expr[][]{{Int.ZERO}};
		Expr[] sq_free = square_free_factorization_integers(u, new Expr[]{x});
		Expr[][] factors = new Expr[sq_free.length][];
		for(int i = 0;i<factors.length;i++)
		{
			Expr f = sq_free[i];
			if(f.isInt())
			{
				factors[i] = new Expr[]{f};
				continue;
			}
			Int content = (Int) GCD.content(f, x, new Expr[]{}, "Z");
			f = f.div(content);
			Expr[] d = factor_monic_hensel(f, x);
			if(!content.equals(Int.ONE))
			    factors[i] = Set.add(new Expr[]{content}, d);
			else
				factors[i] = d;
		}
		return factors;
	}
	
	public static Expr[][] factor_poly_p(Expr u, Expr x, Int p)
	{
		if(u.equals(Int.ZERO))
			return new Expr[][]{{Int.ZERO}};
		Expr[] sq_free = square_free_factorization_p(u, x, p);
		Expr[][] factors = new Expr[sq_free.length][];
		for(int i = 0;i<factors.length;i++)
		{
			Expr f = sq_free[i];
			if(f.isInt())
			{
				factors[i] = new Expr[]{f};
				continue;
			}
			Expr[] d = Factor.berlekamp_factorization(f, x, p);
			factors[i] = d;
		}
		return factors;
	}
	
	public static Expr[][] factor_poly_algebraic_number_field(Expr u, Expr x, Expr p, Expr a)
	{
		if(u.equals(Int.ZERO))
			return new Expr[][]{{Int.ZERO}};
		Expr[] sq_free = square_free_factorization_algebraic_number_field(u, x, new Expr[]{p}, new Expr[]{a});
		Expr[][] factors = new Expr[sq_free.length][];
		Expr x_a = Simplification.getNewVariables(1, u, x, p, a)[0];
		for(int i = 0;i<factors.length;i++)
		{
			Expr f = sq_free[i];
			if(f.isInt())
			{
				factors[i] = new Expr[]{f};
				continue;
			}
			f = Simplification.simplify_recursive(f.substitute(a, x_a));
			Expr[] d = Factor.factor_algebraic_number_field(f, x, x_a, p, a);
			for(int j = 0;j<d.length;j++)
				d[j] = Simplification.simplify_recursive(d[j].substitute(x_a, a));
			factors[i] = d;
		}
		return factors;
	}
	
	public static Expr[] square_free_factorization_rationals(Expr u, Expr x)
	{
		Expr[] vars = Set.add(new Expr[]{x}, Set.complement(Poly.variables(u), new Expr[]{x}));
		Expr[] subs = Simplification.getNewVariables(vars.length, u, x);
		u = u.substitute(vars, subs);
		Expr[] fac = square_free_factorization_rationals(u, subs);
		Expr[] fac_vars = new Expr[fac.length];
		for(int i = 0;i<fac.length;i++)
			fac_vars[i] = Simplification.simplify_recursive(fac[i].substitute(subs, vars));
		return fac_vars;
	}
	
	public static Expr[] square_free_factorization_rationals(Expr u, Expr[] L)
	{
		if(u.equals(Int.ZERO))
			return new Expr[]{Int.ZERO};
		Expr lcm = Poly.coefficient_lcm(u, L);
		u = u.mul(lcm);
		Expr[] factors = square_free_factorization_integers(u, L);
		if(lcm.equals(Int.ONE))
			return factors;
		factors[0] = factors[0].div(lcm);
		return factors;
	}
	
	public static Expr[] square_free_factorization_integers(Expr u, Expr[] L)
	{
		if(u.equals(Int.ZERO))
			return new Expr[]{Int.ZERO};
		Expr x = L[0];
		Expr content = GCD.content(u, x, Set.rest(L), "Z");
		Int lc = (Int)Poly.leading_coef(u, L);
		Expr c = lc.sign().mul(content);
		Expr U = BasicPoly.multivariate_division(u, c, L, "Z")[0];
		Vector<Expr> P = new Vector<Expr>();
		Expr D = Algebra.expand(Diff.derivative(U, x));
		Expr R = GCD.multivariate_gcd(U, D, L, "Z");
		Expr F = BasicPoly.multivariate_division(U, R, L, "Z")[0];
		while(!(Poly.degree(R, x).compareTo(Int.ZERO)<=0))
		{
			Expr G = GCD.multivariate_gcd(R, F, L, "Z");
			Expr s = BasicPoly.multivariate_division(F, G, L, "Z")[0];
			P.add(s);
			R = BasicPoly.multivariate_division(R, G, L, "Z")[0];
			F = G;
		}
		P.add(F);
		P.set(0, Algebra.expand(P.get(0).mul(c)));
		return P.toArray(new Expr[P.size()]);
	}
	
	public static Expr[] square_free_factorization_p(Expr u, Expr x, Int p)
	{
		if(Poly.degree(u, x).compareTo(Int.ONE)<=0)
			return new Expr[]{u};
		Int lc = (Int)Poly.leading_coef(u, x);
		Int lc_inv = lc.modInverse(p);
		u = FiniteField.to_non_negative(Algebra.expand(u.mul(lc_inv)), p);
		Vector<Expr> P = new Vector<Expr>();
		Expr b = FiniteField.to_non_negative(Diff.derivative(u, x), p);
		if(!b.equals(Int.ZERO))
		{
			Expr c = GCD.polynomial_gcd_p(u, b, x, p);
			Expr w = BasicPoly.polynomial_quotient_p(u, c, x, p);
			while(!w.equals(Int.ONE))
			{
				Expr y = GCD.polynomial_gcd_p(w, c, x, p);
				Expr z = BasicPoly.polynomial_quotient_p(w, y, x, p);
				P.add(z);
				w = y;
				c = BasicPoly.polynomial_quotient_p(c, y, x, p);
			}
			if(!c.equals(Int.ONE))
			{
				c = Simplification.simplify_recursive(c.substitute(x, x.pow(Int.ONE.div(p))));
				Expr[] sf = square_free_factorization_p(c, x, p);
				while(P.size()<p.toInt()*sf.length)
					P.add(Int.ONE);
				for(int i = 1;i<=sf.length;i++)
					P.set(i*p.toInt()-1, P.get(i*p.toInt()-1).mul(sf[i-1]));
			}
		}
		else
		{
			u = Simplification.simplify_recursive(u.substitute(x, x.pow(Int.ONE.div(p))));
			Expr[] sf = square_free_factorization_p(u, x, p);
			while(P.size()<p.toInt()*sf.length)
				P.add(Int.ONE);
			for(int i = 1;i<=sf.length;i++)
				P.set(i*p.toInt()-1, P.get(i*p.toInt()-1).mul(sf[i-1]));
		}
		while(P.lastElement().equals(Int.ONE))
			P.removeElementAt(P.size()-1);
		Expr[] factors = P.toArray(new Expr[P.size()]);
		if(factors.length == 0)
			return new Expr[]{lc};
		factors[0] = factors[0].mul(lc);
		return factors;
	}
	
	public static Expr[] square_free_factorization_algebraic_number_field(Expr u, Expr x, Expr[] p, Expr[] a)
	{
		Vector<Expr> P = new Vector<Expr>();
		Expr b = AlgebraicNumberField.simplify_coef(Diff.derivative(u, x), x, p, a);
		Expr c = GCDAlgebraicNumberField.polynomial_gcd(u, b, x, p, a);
		Expr w;
		if(c.equals(Int.ONE))
			w = u;
		else
		{
		    w = AlgebraicNumberField.polynomial_quotient(u, c, x, p, a);
		    Expr y = AlgebraicNumberField.polynomial_quotient(b, c, x, p, a);
		    Expr z = AlgebraicNumberField.simplify_coef(Algebra.expand(y.sub(Diff.derivative(w, x))), x, p, a);
		    while(!z.equals(Int.ZERO))
		    {
		    	Expr g = GCDAlgebraicNumberField.polynomial_gcd(w, z, x, p, a);
		    	P.add(g);
		    	w = AlgebraicNumberField.polynomial_quotient(w, g, x, p, a);
		    	y = AlgebraicNumberField.polynomial_quotient(z, g, x, p, a);
		    	z = AlgebraicNumberField.simplify_coef(Algebra.expand(y.sub(Diff.derivative(w, x))), x, p, a);
		    }
		}
		P.add(w);
		return P.toArray(new Expr[P.size()]);
	}
	
	public static Expr[] polynomial_divisors(Expr[] factors)
	{
		factors = Set.add(factors, new Expr[]{Int.NONE});
		Expr[][] S = Set.subsets(factors);
		Expr[] div = new Expr[S.length];
		for(int i = 0;i<div.length;i++)
		{
			if(S[i].length == 0)
				div[i] = Int.ONE;
			else
			    div[i] = Algebra.expand(Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, S[i])));
		}
		return Set.remove_dublicates(div);
	}
	
	private static Expr[] clean_up(Expr[] w, Expr[] L)
	{
		Expr c = Int.ONE;
		Vector<Expr> v = new Vector<Expr>();
		for(int i = 0;i<w.length;i++)
		{
			if(w[i].isFreeOf(L))
				c = c.mul(w[i]);
			else
				v.add(w[i]);
		}
		if(c.equals(Int.ONE))
			return v.toArray(new Expr[v.size()]);
		return Set.add(new Expr[]{c}, v.toArray(new Expr[v.size()]));
	}
	
	public static Expr[][] multivariate_factorization_rationals(Expr u, Expr[] L)
	{
		if(u.equals(Int.ZERO))
			return new Expr[][]{{Int.ZERO}};
		Int lcm = Poly.coefficient_lcm(u, L);
		u = u.mul(lcm);
		Expr[][] factors = multivariate_factorization_integers(u, L);
		if(factors[0][0].isNumerical())
			factors[0][0] = factors[0][0].div(lcm);
		else
			factors[0] = Set.add(new Expr[]{Int.ONE.division(lcm)}, factors[0]);
	    return factors;	
	}
	
	public static Expr[][] multivariate_factorization_integers(Expr u, Expr[] L)
	{
		if(u.equals(Int.ZERO))
			return new Expr[][]{{Int.ZERO}};
		Expr[] sq_free = square_free_factorization_integers(u, L);
		Expr[][] factors = new Expr[sq_free.length][];
		for(int i = 0;i<factors.length;i++)
		{
			if(sq_free[i].isInt())
				factors[i] = new Expr[]{sq_free[i]};
			else
			    factors[i] = kronecker_factorization(sq_free[i], L);
		}
		return factors;
	}
	
	public static Expr[] kronecker_factorization(Expr u, Expr[] L)
	{
		if(L.length == 0 || u.isInt())
		{
			Int i = (Int)u;
			if(i.abs().equals(Int.ONE))
				return new Expr[]{i};
			if(i.isPositive())
			    return i.factor_list();
			if(i.isNegative())
			{
				i = i.abs();
				return Set.add(new Expr[]{Int.NONE}, i.factor_list());
			}
			return new Expr[]{Int.ZERO};
		}
		
		Expr x = L[0];
		Expr[] R = Set.rest(L);
		if(R.length == 0)
			return Factor.factor_poly_integers_one_list(u, x);
		Expr cont_u = GCD.content(u, x, R, "Z");
		u = BasicPoly.multivariate_division(u, cont_u, L, "Z")[0];
		Int lc = (Int) Poly.leading_coef(u, L);
		if(lc.isNegative())
		{
			u = u.mul(Int.NONE);
			cont_u = cont_u.mul(Int.NONE);
		}
		Expr[] fac_cont = kronecker_factorization(cont_u, R);
		Expr[] fac_u;
		Int n = Poly.degree(u, x);
		if(n.compareTo(Int.ONE)<=0)
			fac_u = new Expr[]{u};
		else
		{
			Int s = n.divide(Int.TWO);
			Expr[][] x_u_values = find_x_u_values(u, s, x);
			Expr[][][] S_sets = find_s_sets(x_u_values, R);
			fac_u = kronecker_factors(S_sets, u, x, R);
		}
		return clean_up(Set.add(fac_cont, fac_u), L);
	}

    

	private static Expr[] kronecker_factors(Expr[][][] sets, Expr u, Expr x, Expr[] R)
	{
		Expr[] L = Set.add(new Expr[]{x}, R);
		int N = 1;
		int[] m = new int[sets.length];
		int[] c = new int[sets.length];
		for(int i = 0;i<sets.length;i++)
		{
			c[i] = 1;
			m[i] = sets[i][1].length;
			N = N*m[i];
		}
		int k = 1;
		while(k <= N)
		{
			Expr[][] points = new Expr[][]{};
			for(int j = 1;j<=sets.length;j++)
			{
				Expr[][] w = sets[j-1];
				Expr X = w[0][0];
				Expr[] S = w[1];
				points = Set.add(new Expr[][]{{X, S[c[j-1]-1]}}, points);
			}
			Expr q = BasicPoly.lagrange_polynomial(points, x);
			if(Poly.degree(q, x).isPositive())
			{
				Expr[] g = BasicPoly.multivariate_division(u, q, L, "Z");
				if(g[1].equals(Int.ZERO))
				{
					Expr v = g[0];
					return Set.add(kronecker_factorization(q, L), kronecker_factorization(v, L));
				}
			}
			int j = 1;
			while(j<=sets.length)
			{
				if(c[j-1]<m[j-1])
				{
					c[j-1] = c[j-1]+1;
					j = sets.length+1;
				}
				else
				{
					c[j-1] = 1;
					j = j + 1;
				}
			}
			k = k + 1;
		}
		return new Expr[]{u};
	}

	private static Expr[][][] find_s_sets(Expr[][] x_u_values, Expr[] R)
	{
		Expr[][][] sets = new Expr[x_u_values.length][2][];
		for(int i = 0;i<sets.length;i++)
		{
			Expr u_i = x_u_values[i][1];
			Expr x_i = x_u_values[i][0];
			Expr[] factor = kronecker_factorization(u_i, R);
			Expr[] factors = new Expr[]{};
			if(u_i.isInt())
				factors = factor;
			else
			{
				for(int j = 0;j<factor.length;j++)
				{
					if(factor[j].isInt())
					{
						Expr[] f = kronecker_factorization(factor[j], new Expr[]{});
						factors = Set.add(factors, f);
					}
					else
						factors = Set.add(factors, new Expr[]{factor[j]});
				}
			}
			Expr[] divisors = polynomial_divisors(factors);
			sets[i] = new Expr[][]{{x_i},divisors};
		}
		return sets;
	}

	private static Expr[][] find_x_u_values(Expr u, Int s, Expr x)
	{
		Int d = Int.ZERO;
		Vector<Expr[]> vals = new Vector<Expr[]>();
		while(vals.size() != s.toInt()+1)
		{
			Expr v = Simplification.simplify_recursive(u.substitute(x, d));
			if(v.equals(Int.ZERO))
			{
				d = d.add(Int.ONE);
				continue;
			}
			else
			{
				vals.add(new Expr[]{d, v});
				d = d.add(Int.ONE);
			}
		}
		return vals.toArray(new Expr[vals.size()][2]);
	}
	
	
	public static Expr[] berlekamp_factorization(Expr u, Expr x, Int p)
	{
		Int n = Poly.degree(u, x);
		if(n.compareTo(Int.ONE) <= 0)
			return new Expr[]{u};
		Int[][] R = r_matrix(u, x, n, p);
		Expr[] S = auxiliary_basis(R, x, n, p);
		if(S.length == 1)
			return new Expr[]{u};
		return find_factors(u, S, x, p);
	}
	
	private static Expr[] find_factors(Expr u, Expr[] S, Expr x, Int p)
	{
		int r = S.length;
		Expr[] factors = {u};
		for(int k = 2;k <= r;k++)
		{
			Expr b = S[k-1];
			Expr[] old_factors = factors;
			for(int i = 1;i <= old_factors.length;i++)
			{
				Expr w = old_factors[i-1];
				Int j = Int.ZERO;
				while(j.compareTo(p.sub(Int.ONE))<=0)
				{
					Expr g = GCD.polynomial_gcd_p(b.sub(j), w, x, p);
					if(g.equals(Int.ONE))
						j = j.add(Int.ONE);
					else if(g.equals(w))
						j = p;
					else
					{
						factors = Set.complement(factors, new Expr[]{w});
						Expr q = BasicPoly.polynomial_quotient_p(w, g, x, p);
						factors = Set.union(factors, new Expr[]{g, q});
						if(factors.length == r)
							return factors;
						else
						{
							j = j.add(Int.ONE);
							w = q;
						}
					}
						
				}
			}
		}
		return factors;
	}
	
	private static Expr[] auxiliary_basis(Int[][] R, Expr x, Int m, Int p)
	{
		int n = m.toInt();
		int[] P = new int[n];
		for(int i = 0;i<P.length;i++)
			P[i] = 0;
		Expr[] S = {};
		for(int j = 1;j<=n;j++)
		{
			int i = 1;
			boolean pivot_found = false;
			while(!pivot_found && i<=n)
			{
				if(!R[i-1][j-1].equals(Int.ZERO) && P[i-1] == 0)
					pivot_found = true;
				else
					i = i + 1;
			}
			if(pivot_found)
			{
				P[i-1] = j;
				Int a = R[i-1][j-1].modInverse(p);
				for(int l = 1;l <= n;l++)
					R[i-1][l-1] = a.mul(R[i-1][l-1]).mod(p);
				for(int k = 1;k <= n;k++)
				{
					if(k != i)
					{
						Int f = R[k-1][j-1];
						for(int l = 1;l <= n;l++)
							R[k-1][l-1] = R[k-1][l-1].sub(f.mul(R[i-1][l-1])).mod(p);
					}
				}
			}
			else
			{
				Expr s = x.pow(new Int(j-1));
				for(int l = 1;l <= j-1;l++)
				{
					int e = 0;
					i = 1;
					while(e == 0 && i <= n)
					{
						if(l == P[i-1])
							e = i;
						else
							i = i + 1;
					}
					if(e > 0)
					{
						Expr c = R[e-1][j-1].mul(Int.NONE).mod(p);
						s = s.add(c.mul(x.pow(new Int(l-1))));
					}
				}
				S = Set.add(S, new Expr[]{s});
			}
		}
		return S;
		
	}
	
	private static Int[][] r_matrix(Expr u, Expr x, Int n, Int p)
	{
	    Expr v = u.sub(x.pow(n));
	    Expr[] rem = new Expr[n.toInt()];
	    Expr prem = Int.ONE;
	    rem[0] = prem;
	    for(Int i = Int.ZERO;i.compareTo(p.mul(n.sub(Int.ONE)))<=0;i = i.add(Int.ONE))
	    {
	    	if(i.mod(p).equals(Int.ZERO))
	    	    rem[i.divide(p).toInt()] = prem;
	    	Expr c = Poly.coefficient_poly(prem, x, n.sub(Int.ONE));
	    	Expr z = Algebra.expand(prem.sub(c.mul(x.pow(n.sub(Int.ONE)))));
	    	prem = FiniteField.to_non_negative(Algebra.expand(x.mul(z).sub(c.mul(v))), p);
	    }
	    Int[][] R = new Int[n.toInt()][n.toInt()];
	    for(int i = 0;i<R.length;i++)
	    {
	    	for(int j = 0;j<R[i].length;j++)
	    	{
	    		if(i == j)
	    			R[i][j] = (Int)FiniteField.to_non_negative(Poly.coefficient_poly(rem[j], x, new Int(i)).sub(Int.ONE), p);
	    		else
	    			R[i][j] = (Int)Poly.coefficient_poly(rem[j], x, new Int(i));
	    	}
	    }
		return R;
	}
	
	public static Expr[] distinct_degree_factorization(Expr a, Expr x, Int p)
	{
		int i = 1;
		Expr w = x;
		Int n = Poly.degree(a, x);
		Expr[] factors = new Expr[n.divide(Int.TWO).toInt()+1];
		factors[0] = Int.ONE;
		while(i <= n.divide(Int.TWO).toInt())
		{
			w = FiniteField.to_non_negative(poly_exp_mod(w, p, a, x, p), p);
			factors[i] = GCD.polynomial_gcd_p(a, w.sub(x), x, p);
			if(!factors[i].equals(Int.ONE))
			{
				a = BasicPoly.polynomial_quotient_p(a, factors[i], x, p);
				w = BasicPoly.polynomial_remainder_p(w, a, x, p);
			}
			i = i + 1;
		}
		Expr[] f = Set.add(factors, new Expr[]{a});
		while(f[f.length-1].equals(Int.ONE))
			f = Set.first(f);
		return f;
	}
	
	public static Expr poly_exp_mod(Expr base, Int p, Expr F, Expr x, Int M)
	{
		Expr prod = Int.ONE;
		base = BasicPoly.polynomial_remainder_p(base, F, x, p);
		while(true)
		{
			if(M.isOdd())
				prod = BasicPoly.polynomial_remainder_p(Algebra.expand(base.mul(prod)), F, x, p);
			M = M.divide(Int.TWO);
			if(M.equals(Int.ZERO))
				return prod;
			else
				base = BasicPoly.polynomial_remainder_p(Algebra.expand(base.mul(base)), F, x, p);
		}
	}
	
	public static Expr[] split_degree_factorization(Expr a, Expr x, Int i, Int p, Int m)
	{
		Int q = (Int) p.pow(m);
		Int n = Poly.degree(a, x);
		if(n.compareTo(i)<=0)
			return new Expr[]{a};
		Expr[] factors = new Expr[]{a};
		while(true)
		{
			Expr v = FiniteField.random_polynomial(x, Int.TWO.mul(i).sub(Int.ONE), q);
			if(p.equals(Int.TWO))
			{
				Expr sum = Int.ZERO;
				Int b = (Int) Int.TWO.pow(m.mul(i).sub(Int.ONE));
				for(Int k = Int.ONE;k.compareTo(b)<=0;k = k.add(Int.ONE))
					sum = sum.add(v.pow(k));
				v = FiniteField.to_non_negative(Algebra.expand(sum), q);
			}
			else
			{
				v = poly_exp_mod(v, p, a, x,  (Int)q.pow(i).sub(Int.ONE).div(Int.TWO)).sub(Int.ONE);
				v = FiniteField.to_non_negative(v, q);
			}
			Expr g = GCD.polynomial_gcd_p(a, v, x, p);
			if(!g.equals(Int.ONE) && !FiniteField.to_non_negative(g.sub(a), p).equals(Int.ZERO))
			{
				Expr[] f1 =  split_degree_factorization(g, x, i, p, m);
				Expr[] f2 =  split_degree_factorization(BasicPoly.polynomial_quotient_p(a, g, x, p), x, i, p, m);
				factors = Set.union(f1, f2);
				return factors;
			}
		}
	}
	
	public static Expr[] factor_cantor_zassenhaus(Expr u, Expr x, Int p)
	{
		Expr[] dd = distinct_degree_factorization(u, x, p);
		Expr[] factors = new Expr[]{dd[0]};
		for(int i = 1;i<dd.length;i++)
		{
			Expr[] sd = split_degree_factorization(dd[i], x, new Int(i), p, Int.ONE);
			factors = Set.add(factors, sd);
		}
		return factors;
	}
	
	public static Expr[] monic_hensel_lift(Expr u, Expr[] S, Expr x, Int p, Int k)
	{
		if(k.equals(Int.ONE))
			return true_factors(u, S, x, p, k);
		else
		{
			Int height = Poly.poly_height(u, x);
			boolean used_try = false;
			Expr[] V = S;
			Expr[] G = sigma_p_2(V, x, p);
			for(Int j = Int.TWO;j.compareTo(k)<=0;j = j.add(Int.ONE))
			{
				Expr Vp = Algebra.expand(Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, V)));
				Expr E = u.sub(Vp);
				if(E.equals(Int.ZERO))
					return V;
				else
				{
					Expr F = Algebra.expand(FiniteField.to_symmetric(E, (Int) p.pow(j)).div(p.pow(j.sub(Int.ONE))));
					Expr[] R = R_p(V, G, F, x, p);
					Expr[] Vnew = new Expr[V.length];
					for(int i = 0;i<V.length;i++)
					{
						Expr v_lift = Algebra.expand(V[i].add(R[i].mul(p.pow(j.sub(Int.ONE)))));
						Vnew[i] = v_lift;
					}
					V = Vnew;
				}
				if(p.pow(j).compareTo(height)>0 && !used_try)
				{
					//Try to check if factors are already in the list
					used_try = true;
					Vector<Expr> factors = new Vector<Expr>();
					Vector<Expr> not_factors = new Vector<Expr>();
					for(int i = 0;i<V.length;i++)
					{
						Expr v = FiniteField.to_symmetric(V[i], p);
						Expr r = BasicPoly.polynomial_division_Q(u, v, x)[1];
						if(r.equals(Int.ZERO))
							factors.add(v);
						else
							not_factors.add(v);
					}
					if(!factors.isEmpty())
					{
						if(not_factors.isEmpty())
							return factors.toArray(new Expr[factors.size()]);
						else
						{
							Expr[] f = factors.toArray(new Expr[factors.size()]);
							Expr[] nf = not_factors.toArray(new Expr[not_factors.size()]);
                            Expr poly = Algebra.expand(Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, f)));
                            Expr v = BasicPoly.polynomial_division_Q(u, poly, x)[0];
                            Int B = find_B(v, x);
                			k = find_k(p, B);
                			Expr[] hl = monic_hensel_lift(v, nf, x, p, k);
                			Expr[] t = true_factors(v, hl, x, p, k);
                			return Set.union(f, t);
						}
					}
				}
			}
			return true_factors(u, V, x, p, k);
		}
	}

	private static Expr[] R_p(Expr[] V, Expr[] G, Expr F, Expr x, Int p)
	{
		Expr[] r = new Expr[V.length];
		for(int i = 0;i<r.length;i++)
		{
			Expr Fs = FiniteField.to_non_negative(Algebra.expand(F.mul(G[i])), p);
			Expr rem = BasicPoly.polynomial_remainder_p(Fs, V[i], x, p);
			r[i] = FiniteField.to_symmetric(rem, p);
		}
		return r;
	}

	private static Expr[] sigma_p(Expr[] V, Expr x, Int p)
	{
		Expr[] g = new Expr[V.length];
		Expr v = Algebra.expand(Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, V)));
		for(int i = 0;i<g.length;i++)
		{
			g[i] = BasicPoly.polynomial_quotient_p(v, V[i], x, p);
		}
		Expr[] gcd = GCD.polynomial_extended_gcd_p(g, x, p);
		for(int i = 0;i<gcd.length;i++)
			gcd[i] = FiniteField.to_symmetric(gcd[i], p);
		return Set.rest(gcd);
	}
	
	//Should be faster
	private static Expr[] sigma_p_2(Expr[] a, Expr x, Int p)
	{
		int r = a.length;
		Expr[] beta = new Expr[r];
	    Expr[] s = new Expr[r];
	    beta[0] = Int.ONE;
	    Expr product = Int.ONE;
	    for(int i = 2;i<=r;i++)
	    	product = Algebra.expand(product.mul(a[i-1]));
	    product = FiniteField.to_symmetric(product, p);
	    for(int j = 1;j<=r-1;j++)
	    {
	    	Expr[] betas = solve_p(a[j-1], product, beta[j-1], x, p);
            beta[j] = betas[0];
            s[j-1] = betas[1];
            //Divide out the a_i's
            product = FiniteField.to_symmetric(BasicPoly.polynomial_quotient_p(product, a[j+1-1], x, p), p);
	    }
		s[r-1] = beta[r-1];
		return s;
	}
	
	public static Expr[] solve_p(Expr a, Expr b, Expr c, Expr x, Int p)
	{
		Expr[] st = GCD.polynomial_extended_gcd_p(a, b, x, p);
		Expr s = st[1];
		Expr t = st[2];
		Expr rho_ = FiniteField.to_symmetric(Algebra.expand(s.mul(c)), p);
		Expr tau_ = FiniteField.to_symmetric(Algebra.expand(t.mul(c)), p);
		Expr[] qr = BasicPoly.polynomial_division_p(rho_, b, x, p);
		Expr q = FiniteField.to_symmetric(qr[0], p);
		Expr r = FiniteField.to_symmetric(qr[1], p);
		return new Expr[]{r, FiniteField.to_symmetric(Algebra.expand(tau_.add(q.mul(a))), p)};
	}
	
	public static Expr[] true_factors(Expr u, Expr[] l, Expr x, Int p, Int k)
	{
		Expr U = u;
		Expr[] L = l;
		Expr[] factors = {};
		int m = 1;
		Int p_k = (Int) p.pow(k);
		while(m <= L.length / 2)
		{
			Expr[][] C = Set.subsets(L, m);
			while(C.length != 0)
			{
				Expr[] t = C[0];
				Expr T = Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, t));
				T = FiniteField.to_symmetric(Algebra.expand(T), p_k);
				Expr[] D = BasicPoly.polynomial_division_Q(U, T, x);
				if(D[1].equals(Int.ZERO))
				{
					factors = Set.union(factors, new Expr[]{T});
					U = D[0];
					L = Set.complement(L, t);
					C = Set.clean_up(C, t);
				}
				else
				    C = Set.complement(C, new Expr[][]{t});
			}
			m = m + 1;
		}
		if(!U.equals(Int.ONE))
			factors = Set.union(factors, new Expr[]{U});
		return factors;
	}
	
	private static Int find_prime(Expr u, Expr x)
	{
		Expr du = Diff.derivative(u, x);
		Int p = new Int(17);
		Expr res = Resultant.resultant_p(u, du, x, p);
		while(res.equals(Int.ZERO))
		{
			p = p.add(Int.TWO);
			if(p.isPrime())
				res = Resultant.resultant_p(u, du, x, p);
		}
		return p;
	}
	
	private static Int find_B(Expr u, Expr x)
	{
		Int n = Poly.degree(u, x);
		Int p = Poly.poly_height(u, x);
		return (Int) Int.TWO.pow(n).mul(Int.ONE.add(n).square_root()).mul(p);
	}
	
	private static Int find_k(Int p, Int B)
	{
		Int B2 = Int.TWO.mul(B);
		Int k = Int.ONE;
		Int f = p;
		while(B2.compareTo(f)>0)
		{
			k = k.add(Int.ONE);
			f = f.mul(p);
		}
		return k;
	}
	
	private static Expr[] factor_monic_hensel(Expr u, Expr x)
	{
		Int n = Poly.degree(u, x);
		Expr l = Poly.coefficient_poly(u, x, n);
		Expr V = Algebra.expand(Simplification.simplify_recursive(u.mul(l.pow(n.sub(Int.ONE))).substitute(x, x.div(l))));
		Int p = find_prime(V, x);
		Expr[] S = berlekamp_factorization(FiniteField.to_non_negative(V, p), x, p);
		if(S.length == 1)
			return new Expr[]{u};
		else
		{
			Int B = find_B(V, x);
			Int k = find_k(p, B);
			for(int i = 0;i<S.length;i++)
				S[i] = FiniteField.to_symmetric(S[i], p);
			Expr[] M = monic_hensel_lift(V, S, x, p, k);
			for(int i = 0;i<M.length;i++)
			{
				M[i] = Simplification.simplify_recursive(M[i].substitute(x, x.mul(l)));
				M[i] = GCD.primitive(M[i], x, new Expr[]{}, "Z");
			}
			return M;
		}
	}
	
	public static Expr[] factor_algebraic_number_field(Expr a, Expr z, Expr alpha, Expr m, Expr x)
	{
		Int s = Int.ZERO;
		Expr a_s = a;
		Expr norm = Resultant.multivariate_resultant(m, a_s.substitute(alpha, x), new Expr[]{x, z}, "Q");
		Expr gcd = GCD.multivariate_gcd(norm, Diff.derivative(norm, z), new Expr[]{z}, "Q");
		while(Poly.degree(gcd, z).compareTo(Int.ZERO)>0)
		{
			s = s.add(Int.ONE);
			a_s = Algebra.expand(a_s.substitute(z, z.sub(alpha)));
		    norm = Resultant.multivariate_resultant(m, a_s.substitute(alpha, x), new Expr[]{x, z}, "Q");
			gcd = GCD.multivariate_gcd(norm, Diff.derivative(norm, z), new Expr[]{z}, "Q");
		}
		Expr[] b = factor_poly_rationals(norm, z)[0];
		if(b.length == 1)
			return new Expr[]{a};
		else
		{
			Expr lcm = Int.ONE;
			for(int i = 0;i<b.length;i++)
			{
				Expr a_i = GCDAlgebraicNumberField.polynomial_gcd(b[i], a_s, z, new Expr[]{m.substitute(x, alpha)}, new Expr[]{alpha});
				a_i = Algebra.expand(a_i.substitute(z, z.add(s.mul(alpha))));
			    a_i = AlgebraicNumberField.simplify_coef(a_i, z, new Expr[]{m.substitute(x, alpha)}, new Expr[]{alpha});
			    Int l = Poly.coefficient_lcm(a_i, new Expr[]{z, alpha});
			    b[i] = a_i.mul(l);
			    lcm = lcm.div(l);
			}
			if(lcm.equals(Int.ONE))
				return b;
			else
			    return Set.add(new Expr[]{lcm}, b);
		}
		
	}
	
	public static Int[] integer_roots(Expr f, Expr x, Int p)
	{
		Expr g = GCD.polynomial_gcd_p(f, x.pow(p).sub(x), x, p);
		Expr[] sd = split_degree_factorization(g, x, Int.ONE, p, Int.ONE);
		Int[] k = new Int[sd.length];
		for(int i = 0;i<sd.length;i++)
			k[i] = ((Int)Poly.coefficient_poly(sd[i], x, Int.ZERO).mul(Int.NONE)).mod(p);
		return k;
	}
	
	public static Expr[] multivariate_hensel(Expr a, Expr[] I, Expr[] Iv, Int p, Int l, Expr[] u, Expr[] lcU, Expr x_1)
	{
		Int pl = (Int) p.pow(l);
		int v = Iv.length + 1;
		Expr[] A = new Expr[v];
		A[v-1] = a;
		Expr[] x = new Expr[v];
		Expr[] alpha = new Expr[v];
		for(int j = v;j<=2;j--)
		{
			x[j-1] = Iv[j-1-1];
			alpha[j-1] = I[j-1-1];
			A[j-1-1] = FiniteField.to_symmetric(Simplification.simplify_recursive(A[j-1].substitute(x[j-1], alpha[j-1])), pl);
		}
		Int maxdeg = Int.ZERO;
		for(int i = 2;i<=v;i++)
		{
			Int d = Poly.degree(a, x[i-1]);
			maxdeg = maxdeg.compareTo(d)<0?d:maxdeg;
		}
		Expr[] U = new Expr[u.length];
		for(int i = 0;i<U.length;i++)
			U[i] = u[i];
		int n = u.length;
		for(int j = 2;j<=v;j++)
		{
			Expr[] U1 = new Expr[U.length];
			for(int i = 0;i<U1.length;i++)
				U1[i] = U[i];
			Expr monomial = Int.ONE;
			for(int m = 1;m<=n;m++)
			{
				if(!lcU[m].equals(Int.ONE))
				{
					Expr[] nI = new Expr[v-1-j+1];
					Expr[] nIv = new Expr[v-1-j+1];
					for(int k = 0;k<nI.length;k++)
					{
						nI[k] = I[j+k];
						nIv[k] = Iv[j+k];
					}
					Expr coef = FiniteField.to_symmetric(Simplification.simplify_recursive(lcU[m].substitute(nI, nIv)), pl);
					U[m] = replace_lc(U[m], x_1, coef);
				}
			}
			Expr e = Algebra.expand(A[j-1].sub(Simplification.expand_product(U)));
			Int degAj = Poly.degree(A[j-1], x[j-1]);
			for(Int k = Int.ONE;k.compareTo(degAj)<=0 && e.equals(Int.ZERO);k = k.add(Int.ONE))
			{
				monomial = Algebra.expand(monomial.mul(x[j-1].sub(alpha[j-1])));
				Expr c = taylor_coef(e, x[j-1], alpha[j-1], k);
				if(!c.equals(Int.ZERO))
				{
					Expr[] nI = new Expr[j-2];
					Expr[] nIv = new Expr[j-2];
					for(int f = 1;f<=j-2;f++)
					{
						nI[f-1] = I[f-1];
						nIv[f-1] = Iv[f-1];
					}
					Expr[] dU = multivariate_diophant(U1, c, nI, nIv, maxdeg, p, l);
					for(int i = 0;i<dU.length;i++)
						dU[i] = Algebra.expand(dU[i].mul(monomial));
					for(int i = 0;i<U.length;i++)
						U[i] = FiniteField.to_symmetric(Algebra.expand(U[i].add(dU[i])), pl);
					e = FiniteField.to_symmetric(Algebra.expand(A[j-1].sub(Simplification.expand_product(U))), pl);
				}
			}
		}
		if(Algebra.expand(a.sub(Simplification.expand_product(U))).equals(Int.ZERO))
		    return U;
		return null;
	}
	
	private static Expr[] multivariate_diophant(Expr[] u1, Expr c, Expr[] nI, Expr[] nIv, Int maxdeg, Int p, Int l)
	{
		return null;
	}

	public static Expr replace_lc(Expr u, Expr x, Expr coef)
	{
		Int n = Poly.degree(u, x);
		Expr r = Algebra.expand(u.sub(Poly.coefficient_poly(u, x, n).mul(x.pow(n))));
		return r.add(coef.mul(x.pow(n)));
	}
	
	public static Expr taylor_coef(Expr u, Expr x, Expr a, Int k)
	{
		return null;
	}
	
}
