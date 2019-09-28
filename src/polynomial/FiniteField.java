package polynomial;

import algebra.Algebra;
import Expression.Expr;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;

public class FiniteField 
{

	public static Expr to_symmetric(Expr u, Int p)
	{
		if(u.isInt())
			return ((Int)u).mod(p).symmetric(p);
		if(u.isSum() || u.isProduct())
		{
			Expr[] n = new Expr[u.length()];
			for(int i = 0;i<n.length;i++)
				n[i] = to_symmetric(u.get(i), p);
			return Simplification.simplify_recursive(new Expr(u.getOperator(), n));
		}
		return u;
	}
	
	public static Expr to_non_negative(Expr u, Int p)
	{
		if(u.isInt())
			return ((Int)u).mod(p);
		if(u.isSum() || u.isProduct())
		{
			Expr[] n = new Expr[u.length()];
			for(int i = 0;i<n.length;i++)
				n[i] = to_non_negative(u.get(i), p);
			return Simplification.simplify_recursive(new Expr(u.getOperator(), n));
		}
		return u;
	}
	
	/**
	 * Builds coefficients using Chinese remainder algorithm coefficient by coefficient
	 * @param u - a polynomial in Z[L]
	 * @param v - a polynomial in Z[l]
	 * @param p - an integer such that gcd(p, q) = 1
	 * @param q - an integer such that gcd(p, q) = 1
	 * @param L - a list of variables
	 * @return the polynomial A such that A mod p = u and A mod q = v
	 */
	public static Expr build_modular_coefficients(Expr u, Expr v, Int p, Int q, Expr[] L)
	{
		//Get a list of monomials of u
		Int[][] monomials_u;
		if(u.isSum())
		{
			monomials_u = new Int[u.length()][];
			for(int i = 0;i<u.length();i++)
			{
				Int[] e = Simplification.castToInt(Poly.coefficient_monomial(u.get(i), L)[1]);
				monomials_u[i] = e;
			}
		}
		else
		{
			monomials_u = new Int[][]{Simplification.castToInt(Poly.coefficient_monomial(u, L)[1])};
		}
		//Get a list of monomials of v
		Int[][] monomials_v;
		if(v.isSum())
		{
			monomials_v = new Int[v.length()][];
			for(int i = 0;i<v.length();i++)
			{
				Int[] e = Simplification.castToInt(Poly.coefficient_monomial(v.get(i), L)[1]);
				monomials_v[i] = e;
			}
		}
		else
		{
			monomials_v = new Int[][]{Simplification.castToInt(Poly.coefficient_monomial(v, L)[1])};
		}
		Int[][] union = Set.union(monomials_u, monomials_v);
		Expr poly = Int.ZERO;
		for(int i = 0;i<union.length;i++)
		{
			Int a = (Int) Poly.coefficient_poly(u, L, union[i]);
			Int b = (Int) Poly.coefficient_poly(v, L, union[i]);
			Int c = Int.integer_chinese_remainder_garner(new Int[]{a, b}, new Int[]{p, q});
			//build monomial
			Expr monomial = Int.ONE;
			for(int j = 0;j<L.length;j++)
				monomial = monomial.mul(L[j].pow(union[i][j]));
			poly = poly.add(c.mul(monomial));
		}
		return poly;
	}
	
	/**
	 * Builds coefficients using Chinese remainder algorithm on whole polynomial 
	 * @param U - a list of polynomials with coefficients in Z
	 * @param M - a list of integers
	 * @return the polynomial A such that A mod M[i] = U[i]
	 */
	public static Expr integer_chinese_remainder_garner(Expr[] U, Int[] M)
	{
		int n = M.length-1;
		Int[] gamma = new Int[n+1];
		for(int k = 1;k<=n;k++)
		{
			Int product = M[0].mod(M[k]).symmetric(M[k]);
			for(int i = 1;i<=k-1 && k-1>=1;i++)
			{
				product = product.mul(M[i]).mod(M[k]).symmetric(M[k]);
			}
			gamma[k] = product.modInverse(M[k]).symmetric(M[k]);
		}
		Expr[] v = new Expr[n+1];
		v[0] = U[0];
		for(int k = 1;k<=n;k++)
		{
			Expr tmp = v[k-1];
			for(int j = k-2;j >=0;j--)
				tmp = to_symmetric(Algebra.expand(tmp.mul(M[j]).add(v[j])), M[k]);
			v[k] = to_symmetric(Algebra.expand(U[k].sub(tmp).mul(gamma[k])), M[k]);
		}
		Expr u = v[n];
		for(int k = n-1;k>=0;k--)
			u = u.mul(M[k]).add(v[k]);
		return u;
		
	}
	
	public static Expr newton_interpolation(Int[] alpha, Expr[] u, Expr x, Int p)
	{
		//Symmetric Representation
		for(int i = 0;i<alpha.length;i++)
			alpha[i] = alpha[i].symmetric(p);
		
		
		int n = alpha.length-1;
		Int[] gamma = new Int[n+1];
		for(int k = 1;k<=n;k++)
		{
			Int product = alpha[k].sub(alpha[0]).mod(p).symmetric(p);
			for(int i = 1;i<=k-1 && k-1>=1;i++)
			{
				product = product.mul(alpha[k].sub(alpha[i])).mod(p).symmetric(p);
			}
			gamma[k] = product.modInverse(p).symmetric(p);
		}
		Expr[] v = new Expr[n+1];
		v[0] = u[0];
		for(int k = 1;k<=n;k++)
		{
			Expr tmp = v[k-1];
			for(int j = k-2;j >=0;j--)
				tmp = to_symmetric(tmp.mul(alpha[k].sub(alpha[j])).add(v[j]), p);
			v[k] = to_symmetric(Algebra.expand(u[k].sub(tmp).mul(gamma[k])), p);
		}
		Expr U = v[n];
		for(int k = n-1;k>=0;k--)
			U = to_symmetric(Algebra.expand(U.mul(x.sub(alpha[k])).add(v[k])), p);
		return U;
	}
	
	public static Expr random_polynomial(Expr x, Int n, Int p)
	{
		Expr poly = Int.ZERO;
		for(Int i = Int.ZERO;i.compareTo(n)<=0;i = i.add(Int.ONE))
		{
			Int coef = Int.random_int(Int.ZERO, p.sub(Int.ONE));
			while(i.equals(n) && coef.equals(Int.ZERO))
				coef = Int.random_int(Int.ZERO, p.sub(Int.ONE));
			poly = poly.add(coef.mul(x.pow(i)));
		}
		return poly;
	}
	
	
}
