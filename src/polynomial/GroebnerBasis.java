package polynomial;

import algebra.Algebra;
import Expression.Expr;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;

public class GroebnerBasis 
{   
	
	public static Constant DEFAULT_ORDER = Constant.LEXOGRAPHIC;
	
	/**
	 * Reduction of a multivariate polynomial 
	 * @param u - a multivariate polynomial in Q[L]
	 * @param F - a list of multivariate polynomials in Q[L]
	 * @param L - a list of variables
	 * @return the reduced polynomial with respect to the side relations F = 0
	 */
    public static Expr[][] reduction(Expr u, Expr[] F, Expr[] L, Constant D)
    {
    	Expr R = u;
    	Expr r = Int.ZERO;
    	Expr[] c = new Expr[F.length];
    	for(int i = 0;i<F.length;i++)
    		c[i] = Int.ZERO;
    	int i = 1;
    	while(!R.equals(Int.ZERO))
    	{
    		Expr m = GroebnerBasis.leading_monomial(R, L, D);
    		Expr f = F[i-1];
    		Expr lmf = GroebnerBasis.leading_monomial(f, L, D);
    		Expr Q = m.div(lmf);
    		if(Poly.is_poly(Q, L))
    		{
    			R = Cancel.simplify(R.sub(Q.mul(f)), L);
    			c[i-1] = Cancel.simplify(c[i-1].add(Q), L);
    			i = 1;
    		}
    		else
    			i = i + 1;
    		if(i == F.length+1)
    		{
    			R = Cancel.simplify(R.sub(m), L);
    			r = Cancel.simplify(r.add(m), L);
    			i = 1;
    		}
    	}
    	return new Expr[][]{c, {r}};
    }
    
    /**
     * Least common multiple of two monomials
     * @param u - a nonzero monomial in Q[L]
     * @param v - a nonzero monomial in Q[L]
     * @param L - a list of variables
     * @return lcm(u, v)
     */
    public static Expr monomial_lcm(Expr u, Expr v, Expr[] L)
    {
    	Expr lcm = Int.ONE;
    	for(int i = 0;i<L.length;i++)
    	{
    		Int n = Poly.degree(u, L[i]);
    		Int m = Poly.degree(v, L[i]);
    		lcm = lcm.mul(L[i].pow(Int.max(n, m)));
    	}
    	return lcm;
    }
    
    /**
     * S-polynomial in Q[L]
     * @param u - a nonzero multivariate polynomial in Q[L]
     * @param v - a nonzero multivariate polynomial in Q[L]
     * @param L - a list of variables
     * @return S-polynomial of 
     */
    public static Expr S_polynomial(Expr u, Expr v, Expr[] L, Constant D)
    {
    	Expr lmu = GroebnerBasis.leading_monomial(u, L, D);
    	Expr lmv = GroebnerBasis.leading_monomial(v, L, D);
    	Expr d = monomial_lcm(lmu, lmv, L);
    	return Cancel.simplify((d.div(lmu).mul(u).sub(d.div(lmv).mul(v))), L);
    }
     
    /**
     * Groebner basis of an Ideal
     * @param F - a list of multivariate polynomials in Q[L]
     * @param L - a list of variables
     * @return the list G of polynomials in Q[L] such that {F} = {G} and G is a Groebner basis 
     */
    public static Expr[] groebner_basis(Expr[] F, Expr[] L, Constant D)
    {
    	Expr[] G = F;
    	Expr[][] P = new Expr[][]{};
    	for(int i = 0;i<G.length;i++)
    		for(int j = i+1;j<G.length;j++)
    			P = Set.add(P, new Expr[][]{{G[i], G[j]}});
    	while(P.length != 0)
    	{
    		Expr[] t = P[0];
    		P = Set.rest(P);
    		Expr s = S_polynomial(t[0], t[1], L, D);
    		Expr r = reduction(s, G, L, D)[1][0];
    		if(!r.equals(Int.ZERO))
    		{
    			for(int i = 0;i<G.length;i++)
    				P = Set.add(P, new Expr[][]{{G[i], r}});
    			G = Set.add(G, new Expr[]{r});
    		}
    	}
    	return G;
    }
    
    public static Expr[] groebner_basis_improved(Expr[] F, Expr[] L, Constant D)
    {
    	Expr[] G = F;
    	int k = G.length;
    	Expr[][] P = new Expr[][]{};
    	for(int i = 1;i<=k;i++)
    		for(int j = i+1;j<=k;j++)
    			P = Set.add(P, new Expr[][]{{new Int(i), new Int(j)}});
    	while(P.length != 0)
    	{
    		Expr[] t = P[0];
    		P = Set.rest(P);
    		int i = ((Int)t[0]).toInt();
    		int j = ((Int)t[1]).toInt();
    		if((criterion_1(i, j, G, L, D) && 
    				criterion_2(i, j, P, G, L, D)))
    		{
    			Expr s = S_polynomial(G[i-1], G[j-1], L, D);
    			Expr r = reduction(s, G, L, D)[1][0];
    			if(!r.equals(Int.ZERO))
    			{
    				G = Set.add(G, new Expr[]{r});
    				k = k+1;
    				for(int l = 1;l<k;l++)
    					P = Set.add(P, new Expr[][]{{new Int(l), new Int(k)}});
    			}
    		}
    	}
    	return G;
    }
    
    private static boolean criterion_2(int i, int j, Expr[][] B, Expr[] G, Expr[] L, Constant D) 
    {
    	Expr lcm = monomial_lcm(G[i-1], G[j-1], L);
		for(int k = 1;k<=G.length;k++)
		{
			if(k == i || k == j)
				continue;
			Expr Gk = h_term(G[k-1], L, D);
			if(Poly.is_poly(lcm.div(Gk), L))
			{
				if(!Set.member(B, new Expr[]{new Int(i), new Int(k)})
						&& !Set.member(B, new Expr[]{new Int(k), new Int(j)}))
					return false;
			}
		}
		return true;
	}

	private static boolean criterion_1(int i, int j, Expr[] G, Expr[] L, Constant D)
    {
		Expr Gi = GroebnerBasis.h_term(G[i-1], L, D);
		Expr Gj = GroebnerBasis.h_term(G[j-1], L, D);
		Expr lcm = monomial_lcm(Gi, Gj, L);
		if(!lcm.equals(Gi.mul(Gj)))
			return true;
		return false;
	}

	/**
     * Elimination of redundant polynomials 
     * @param G - a list of multivariate polynomials in Q[L]
     * @param L - a list of variables
     * @return the reduced list F such that \<F\> is an Groebner basis and \<F\> = \<G\>
     */
    public static Expr[] reduce_basis(Expr[] G, Expr[] L, Constant D)
    {
    	for(int i = 0;i<G.length;i++)
    	{
    		Expr[] F = Set.remove(G, i);
            if(F.length == 0)
            	break;
    		Expr r = reduction(G[i], F, L, D)[1][0];
    		if(r.equals(Int.ZERO))
    		{
    			G = F;
    			i = i - 1;
    		}
    	}
    	if(G.length == 1)
    		return G;
    	Expr[] E = new Expr[]{};
    	for(int i = 0;i<G.length;i++)
    	{
    		Expr h = reduction(G[i], Set.complement(G, new Expr[]{G[i]}), L, D)[1][0];
    		E = Set.union(E, new Expr[]{h});
    	}
    	return E;
    }
    
    public static Expr[] reduced_groebner(Expr[] G, Expr[] L, Constant D)
    {
    	Expr[] F = groebner_basis(G, L, D);
    	Expr[] R = reduce_basis(F, L, D);
    	return R;
    }
    
    
    /**
     * Simplification of a polynomial
     * @param u - a multivariate polynomial in Q[L]
     * @param F - a list of multivariate polynomials in Q[L]
     * @param L - a list of variables
     * @return null if F is inconsistent, the simplified form of u otherwise
     */
    public static Expr simplify_poly(Expr u, Expr[] F, Expr[] L)
    {
    	Expr[] G = groebner_basis(F, L, Constant.REVGRADLEX);
    	Expr[] H = reduce_basis(G, L, Constant.REVGRADLEX);
    	if(H.length == 1 && H[0].isFreeOf(L))
    		return null;
    	else
    		return reduction(u, H, L, Constant.REVGRADLEX)[1][0];
    }
    
    public static Expr leading_monomial(Expr u, Expr[] L, Constant D)
	{
		if(D.equals(Constant.LEXOGRAPHIC))
			return leading_monomial_lex(u, L);
		if(D.equals(Constant.REVGRADLEX))
			return leading_monomial_total(u, L);
		return null;
	}

	public static Expr leading_monomial_lex(Expr u, Expr[] L)
	{
		if(u.equals(Int.ZERO))
			return Int.ZERO;
		if(L.length == 0)
			return u;
		Expr x = L[0];
		Expr[] R = Set.rest(L);
		Int n = Poly.degree(u, x);
		Expr c = Poly.coefficient_poly(u, x, n);
		return x.pow(n).mul(leading_monomial_lex(c, R));
	}
	
	public static Expr leading_monomial_total(Expr u, Expr[] L)
	{
		if(u.isSum())
		{
			Expr lm = null;
			for(int i = 0;i<u.length();i++)
			{
				if(lm == null)
					lm = u.get(i);
				else
				{
					lm = compare_monomial_total(u.get(i), lm, L)>0?u.get(i):lm;
				}
			}
			return lm;
		}
		return u;
	}
	
	public static int compare_monomial_total(Expr u, Expr v, Expr[] L)
	{
		Expr[] du = Poly.coefficient_monomial(u, L)[1];
		Expr[] dv = Poly.coefficient_monomial(v, L)[1];
		Int sum_u = Int.ZERO, sum_v = Int.ZERO;
		for(int i = 0;i<du.length;i++)
		{
			sum_u = sum_u.add((Int)du[i]);
			sum_v = sum_v.add((Int)dv[i]);
		}
		int f = sum_u.compareTo(sum_v);
		if(f != 0)
			return f;
		for(int i = L.length-1;i>=0;i--)
		{
			Int U = Poly.degree(u, L[i]);
			Int V = Poly.degree(v, L[i]);
			int g = U.compareTo(V);
			if(g != 0)
				return g;
		}
		return 0;
	}
	
	public static Expr h_term(Expr u, Expr[] L, Constant D)
	{
		if(u.equals(Int.ZERO))
			return Int.ONE;
		Expr lm = leading_monomial(u, L, D);
		Expr ht = Simplification.constant_term(lm, L)[1];
		return ht;
	}
	
	public static Expr[] reducer_set(Expr p, Expr[] Q, Expr[] L, Constant D)
	{
		Expr[] R = new Expr[]{};
		Expr htp = h_term(p, L, D);
		for(int i = 0;i<Q.length;i++)
		{
			if(Q[i].equals(Int.ZERO))
				continue;
			Expr htQ = h_term(Q[i], L, D);
			if(Poly.is_poly(htp.div(htQ), L))
				R = Set.add(R, new Expr[]{Q[i]});
		}
		return R;
	}
    
    
}
