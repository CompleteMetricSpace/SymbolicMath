package polynomial;

import solve.LinearAlgebra;
import algebra.Algebra;
import Expression.Expr;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;

public class Decompose
{
    public static Expr[] decompose(Expr u, Expr x)
    {
    	Expr U = u.sub(Poly.coefficient_poly(u, x, Int.ZERO));
    	Expr[] factors = Factor.factor_poly_rationals_one_list(U, x);
    	Expr[] S = Factor.polynomial_divisors(factors);
    	Expr[] decomposition = new Expr[]{};
    	Expr C = x;
    	Expr t = Simplification.getNewVariables(1, u, x)[0];
    	Expr final_component = null;
    	while(S.length != 0)
    	{
    		Expr w = find_min_deg(S, x);
    		S = Set.complement(S, new Expr[]{w});
    		Int dw = Poly.degree(w, x);
    		Int du = Poly.degree(u, x);
    		if(Poly.degree(C, x).compareTo(dw)<0 && dw.compareTo(du)<0 && du.mod(dw).equals(Int.ZERO))
    		{
    			Expr g = BasicPoly.polynomial_expansion(w, C, x, t);
    			Expr R = BasicPoly.polynomial_expansion(u, w, x, t);
    			if(g.isFreeOf(x) && R.isFreeOf(x))
    			{
    				decomposition = Set.add(new Expr[]{g.substitute(t, x)}, decomposition);
    				C = w;
    				final_component = R;
    			}
    		}
    	}
    	if(decomposition.length == 0)
    		return new Expr[]{u};
    	else
    		return Set.add(new Expr[]{final_component.substitute(t, x)}, decomposition);
    }

	private static Expr find_min_deg(Expr[] s, Expr x)
	{
		if(s.length == 1)
			return s[0];
		Int d = Poly.degree(s[0], x);
		Expr p = s[0];
		for(int i = 1;i<s.length;i++)
		{
			Int k = Poly.degree(s[i], x);
			if(k.compareTo(d)<0)
			{
				d = k;
				p = s[i];
			}
		}
		return p;
	}
	
	public static Expr[] decompose_fast(Expr u, Expr x)
	{
		Expr lc = Poly.leading_coef(u, x);
		u = Algebra.expand(u.div(lc));
		Expr[] decompose = decompose_without_factorization(u, x);
		decompose[0] = Algebra.expand(lc.mul(decompose[0]));
		return decompose;
	}
	
	private static Expr[] decompose_without_factorization(Expr u, Expr x)
	{
		Int n = Poly.degree(u, x);
		if(n.compareTo(Int.TWO) <= 0)
			return new Expr[]{u};
		for(Int i = Int.TWO;i.compareTo(n)<0;i = i.add(Int.ONE))
		{
			if(n.mod(i).equals(Int.ZERO))
			{
				Int s = n.divide(i);
				Expr[] d = decomposition_s(u, x, s);
				if(d != null)
				{
					Expr h = d[0];
					Expr g = d[1];
					Expr[] dh = decompose_without_factorization(h, x);
					Expr[] dg = decompose_without_factorization(g, x);
					return Set.add(dh, dg);
				}
			}
		}
		return new Expr[]{u};
	}
	
	public static Expr[] decomposition_s(Expr f, Expr x, Int s)
	{
		Int n = Poly.degree(f, x);
		Int r = n.divide(s);
		Expr[][] q = new Expr[r.toInt()+1][s.toInt()-1+1];
		for(int i = 0;i <= r.toInt();i++)
			q[i][0] = x.pow(new Int(i).mul(s));
		for(int k = 1;k<=s.toInt()-1;k++)
		{
			Expr d = Poly.coefficient_poly(q[r.toInt()][k-1], x, n.sub(new Int(k)));
			Expr c = Poly.coefficient_poly(f, x, n.sub(new Int(k))).sub(d).div(r);
			for(int j = 0;j<=r.toInt();j++)
			{
				q[j][k] = Int.ZERO;
				for(int i = 0;i<=j;i++)
				{
					Expr t = x.pow(new Int(i).mul(s.sub(new Int(k))));
					Expr cp = (c.equals(Int.ZERO) && i == 0)?Int.ONE:c.pow(new Int(i));
					q[j][k] = q[j][k].add(Int.binom(new Int(j), new Int(i)).mul(cp.mul(t.mul(q[j-i][k-1]))));
				}
				q[j][k] = Algebra.expand(q[j][k]);
			}
		}
		Expr h = q[1][s.toInt()-1];
		Expr t = Simplification.getNewVariables(1, f, x)[0];
		Expr g = BasicPoly.polynomial_expansion(f, h, x, t);
		if(g.isFreeOf(x))
			return new Expr[]{g.substitute(t, x), h};
		return null;
	}
}
