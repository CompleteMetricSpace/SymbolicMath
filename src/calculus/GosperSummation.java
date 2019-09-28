package calculus;

import algebra.Algebra;
import polynomial.BasicPoly;
import polynomial.Factor;
import polynomial.GCD;
import polynomial.Poly;
import solve.LinearAlgebra;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;

public class GosperSummation 
{

	public static Int[] prime_dispersion(Expr s, Expr t, Expr k)
	{
		Int n = Poly.degree(s, k);
		if(!n.equals(Poly.degree(t, k)))
			return new Int[]{};
		Expr a = Poly.coefficient_poly(s, k, n);
		Expr b = Poly.coefficient_poly(s, k, n.sub(Int.ONE));
		Expr c = Poly.coefficient_poly(t, k, n);
		Expr d = Poly.coefficient_poly(t, k, n.sub(Int.ONE));
		Expr j = b.mul(c).sub(a.mul(d)).div(a.mul(c.mul(n)));
		if(j.isInt() && ((Int) j).isPositive() || j.equals(Int.ZERO))
		{
			Expr z = Algebra.rationalize_expand((c.mul(s).sub(a.mul(t.substitute(k, k.add(j))))));
			if(z.equals(Int.ZERO))
				return new Int[]{(Int)j};
			return new Int[]{};
		}
		else
			return new Int[]{};
	}
	
	public static Int[] dispersion_set(Expr q, Expr r, Expr k)
	{
		Expr[] f_q = Factor.factor_poly_rationals_distinct(q);
		Expr[] f_r = Factor.factor_poly_rationals_distinct(r);
		Int[] J = new Int[]{};
		for(int i = 0;i<f_q.length;i++)
		{
			for(int j = 0;j<f_r.length;j++)
			{
				J = Set.union(J, prime_dispersion(f_q[i], f_r[j], k));
			}
		}
		return J;
	}
	
	public static Int get_degree_bound(Expr q, Expr r, Expr p, Expr k)
	{
		Expr u_1 = Algebra.expand(q.substitute(k, k.add(Int.ONE)).add(r));
		Expr u_2 = Algebra.expand(q.substitute(k, k.add(Int.ONE)).sub(r));
		Int d = Poly.degree(u_2, k);
		Int n = Poly.degree(u_1, k);
		if(Poly.degree(u_1, k).compareTo(d)<=0)
		{
			return Poly.degree(p, k).sub(d);
		}
		else
		{
			Expr a = Poly.coefficient_poly(u_1, k, n);
			Expr b = Poly.coefficient_poly(u_2, k, n.sub(Int.ONE));
			Expr s = Int.TWO.mul(Int.NONE.mul(b)).div(a);
			if(s.isInt() && ((Int)s).isPositive() || s.equals(Int.ZERO))
				return Int.max((Int)s, Poly.degree(p, k).sub(n).add(Int.ONE));
			else
				return Poly.degree(p, k).sub(n).add(Int.ONE);
		}
	}
	
	public static Expr[] gosper_summation(Expr u, Expr v, Expr k)
	{
		Expr p = Int.ONE;
		Expr q = Algebra.expand(u.substitute(k, k.sub(Int.ONE)));
		Expr r = Algebra.expand(v.substitute(k, k.sub(Int.ONE)));
		Int[] J = dispersion_set(q, r, k);
		while(J.length != 0)
		{
			Int j = J[0];
			Expr g = GCD.multivariate_gcd(q, Algebra.expand(r.substitute(k, k.add(j))), "Q");
			q = BasicPoly.polynomial_quotient(q, g, k);
			r = BasicPoly.polynomial_quotient(r, Algebra.expand(g.substitute(k, k.sub(j))), k);
			Expr prod = Int.ONE;
			for(Int i = Int.ZERO;i.compareTo(j)<0;i = i.add(Int.ONE))
				prod = Algebra.expand(prod.mul(g.substitute(k, k.sub(i))));
			p = Algebra.expand(p.mul(prod));
			J = dispersion_set(q, r, k);
		}
		Int degree = get_degree_bound(q, r, p, k);
		if(degree.isNegative())
			return null;
		Expr f = Int.ZERO;
		Expr[] c = Simplification.getNewVariables(degree.toInt()+1, p, r, q, k);
		for(int i = 0;i<=degree.toInt();i++)
			f = f.add(c[i].mul(k.pow(new Int(i))));
		Expr eq = Algebra.expand(q.substitute(k, k.add(Int.ONE)).mul(f).sub(r.mul(f.substitute(k, k.sub(Int.ONE)))).sub(p));
		int deg = Poly.degree(eq, k).toInt();
		Expr[][] A = new Expr[deg+1][c.length];
		Expr[] B = new Expr[deg+1];
		for(int i = 0;i<A.length;i++)
		{
			Expr coef = Poly.coefficient_poly(eq, k, new Int(i));
			for(int j = 0;j<A[i].length;j++)
			{
				A[i][j] = Poly.coefficient_poly(coef, c[j], Int.ONE);
			}
			B[i] = Poly.coefficient_poly(coef, c, Int.getIntList(Int.ZERO, c.length)).mul(Int.NONE);
		}
		Expr[] x = LinearAlgebra.solve_system(A, B);
		if(x == null)
			return null;
		Expr F = Int.ZERO;
		for(int i = 0;i<x.length;i++)
			F = F.add(x[i].mul(k.pow(new Int(i))));
		return new Expr[]{r, p, F};
	}
	
	public static Expr[] get_u_v(Expr a, Expr k)
	{
		Expr a_k = a.substitute(k, k.add(Int.ONE));
		Expr w = a_k.div(a);
		w = substitute_integer_functions(w);
		w = simplify_integer_functions(w);
		w = Algebra.cancel(w);
		Expr[] nd = Algebra.NumeratorDenominator(w);
		Expr n = nd[0];
		Expr d = nd[1];
		if(Poly.is_poly(n, k) && Poly.is_poly(d, k))
			return new Expr[]{n, d};
		return null;
	}
	
	private static Expr substitute_integer_functions(Expr a) 
	{
		if(a.isSymbolic())
			return a;
		Expr[] op = new Expr[a.length()];
		for(int i = 0;i<a.length();i++)
			op[i] = substitute_integer_functions(a.get(i));
		Expr b = new Expr(a.getOperator(), op);
		if(b.getOperator().equals(Operator.BINOMIAL))
		{
			Expr c = b.get(0);
			Expr d = b.get(1);
			return new Expr(Operator.FACTORIAL, c).div(new Expr(Operator.FACTORIAL, d).mul(new Expr(Operator.FACTORIAL, c.sub(d))));
		}
		return b;
	}
	
	public static Expr simplify_integer_functions(Expr a)
	{
		if(a.isSymbolic())
			return a;
		Expr[] op = new Expr[a.length()];
		for(int i = 0;i<a.length();i++)
			op[i] = simplify_integer_functions(a.get(i));
		Expr b = new Expr(a.getOperator(), op);
		if(b.getOperator().equals(Operator.FACTORIAL))
		{
			Expr c = b.get(0);
			if(c.isSum())
			{
				Expr n = c.get(0);
				Expr v = Simplification.simplify_recursive(new Expr(Operator.ADD, Set.rest(c.getOperands())));
				if(n.isInt())
				{
					Int N = (Int)n;
					if(N.isPositive())
					{
						Expr s = Int.ONE;
						for(Int i = Int.ONE;i.compareTo(N)<=0;i = i.add(Int.ONE))
							s = s.mul(v.add(i));
						return s.mul(new Expr(Operator.FACTORIAL, v));
					}
					else
					{
						Expr s = Int.ONE;
						for(Int i = Int.ZERO;i.compareTo(N)>0;i = i.sub(Int.ONE))
							s = s.mul(v.add(i));
						return new Expr(Operator.FACTORIAL, v).div(s);
					}
				}
			}
		}
		return b;
	}
	
	public static Expr gosper(Expr a, Expr k)
	{
		Expr[] uv = get_u_v(a, k);
		if(uv == null)
			return null; //Not a hypergeometric term
		Expr u = uv[0];
		Expr v = uv[1];
		return gosper(a, u, v, k);
	}
	
	public static Expr gosper(Expr a, Expr u, Expr v, Expr k)
	{
		Expr[] rpf = gosper_summation(u, v, k);
		if(rpf == null)
			return null;
		Expr r = rpf[0], p = rpf[1], f = rpf[2];
		Expr S = r.div(p).mul(f.substitute(k, k.sub(Int.ONE))).mul(a);
		return Algebra.cancel(S);
	}
}
