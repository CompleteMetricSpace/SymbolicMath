package calculus;

import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;
import Symbolic.Rational;
import algebra.Algebra;
import algebra.AlgebraicNumberField;
import polynomial.BasicPoly;
import polynomial.Factor;
import polynomial.GCD;
import polynomial.GCDAlgebraicNumberField;
import polynomial.Poly;
import polynomial.Resultant;
import solve.PolySolve;
import Expression.Expr;
import Expression.Operator;


public class RationalIntegrate 
{
	/**
	 * Integration of a rational function in Q(x)
	 * @param p - a polynomial in Q[x]
	 * @param q - p polynomial in Q[x]
	 * @param x - a variable
	 * @return the function g such that diff(g, x) = p/q
	 */
	public static Expr integrate_rational_function(Expr p, Expr q, Expr x)
	{
	    return integrate_rational_function(p, q, x, true);
	}
	
	/**
	 * Integration of a rational function in Q(x)
	 * @param p - a polynomial in Q[x]
	 * @param q - a polynomial in Q[x]
	 * @param x - a variable
	 * @return the list [[v_0], [c_1, v_1], ..., [c_k, v_k]] such that <br>
	 * p/q = diff(v_0, x) + sum(c_i*diff(v_i, x)/v_i, i, 1, k)
	 */
	public static Expr[][] integrate_rational_function_list(Expr p, Expr q, Expr x)
	{
		Expr[] gh = hermite_reduction(p, q, x);
		Expr[] nd = Algebra.NumeratorDenominator(gh[1]);
		Expr[] qr = BasicPoly.polynomial_division(nd[0], nd[1], x);
		if(qr[1].equals(Int.ZERO))
			return new Expr[][]{{gh[0].add(integrate_poly(qr[0], x))}};
		Expr[][] log = logarithmic_part(qr[1], nd[1], x);
		return Set.add(new Expr[][]{{gh[0].add(integrate_poly(qr[0], x))}}, log);
	}
	
	/**
     * Integration of a rational function in Q(x)
	 * @param p - a polynomial in Q[x]
	 * @param q - a polynomial in Q[x]
	 * @param x - a variable
	 * @param arctan - a boolean 
	 * @return the function g such that diff(g, x) = p/q. <br>
	 * if arctan == true, g is a sum of real logs and arctangents with polynomial arguments. <br>
	 * if arctan == false, g is a sum of real and complex logarithms.
	 */
	public static Expr integrate_rational_function(Expr p, Expr q, Expr x, boolean arctan)
	{
		Expr[] gh = hermite_reduction(p, q, x);
		Expr[] nd = Algebra.NumeratorDenominator(gh[1]);
		Expr[] qr = BasicPoly.polynomial_division(nd[0], nd[1], x);
		if(qr[1].equals(Int.ZERO))
			return gh[0].add(integrate_poly(qr[0], x));
		Expr[][] log = logarithmic_part(qr[1], nd[1], x);
		if(!arctan || log.length < 2)
		{
			Expr log_part = Int.ZERO;
			for(int i = 0;i<log.length;i++)
				log_part = log_part.add(log[i][0].mul(new Expr(Operator.LOG, log[i][1])));
			return log_part.add(gh[0].add(integrate_poly(qr[0], x)));
		}
		else
		{
			Expr log_part = Int.ZERO;
			int i = 1;
			while(i < log.length)
			{
				Expr[] log_1 = log[i-1];
				Expr[] log_2 = log[i];
				Expr c_1 = Algebra.expand(log_1[0]), c_2 = Algebra.expand(log_2[0]);
				Expr v_1 = Algebra.expand(log_1[1]), v_2 = Algebra.expand(log_2[1]);
				Expr x_1 = Poly.coefficient_poly(c_1, Constant.I, Int.ZERO);
				Expr x_2 = Poly.coefficient_poly(c_2, Constant.I, Int.ZERO);
				Expr y_1 = Poly.coefficient_poly(c_1, Constant.I, Int.ONE);
				Expr y_2 = Poly.coefficient_poly(c_2, Constant.I, Int.ONE);
				if(!y_1.equals(Int.ZERO) && Algebra.expand(y_1.add(y_2)).equals(Int.ZERO) && x_1.equals(x_2))
				{
					Expr A_1 = Poly.coefficient_poly(v_1, Constant.I, Int.ZERO);
					Expr A_2 = Poly.coefficient_poly(v_2, Constant.I, Int.ZERO);
					Expr B_1 = Poly.coefficient_poly(v_1, Constant.I, Int.ONE);
					Expr B_2 = Poly.coefficient_poly(v_2, Constant.I, Int.ONE);
					if(Algebra.expand(A_1.sub(A_2)).equals(Int.ZERO) && Algebra.expand(B_1.add(B_2)).equals(Int.ZERO) && !B_1.equals(Int.ZERO))
					{
						log_part = log_part.add(x_1.mul(new Expr(Operator.LOG, Algebra.expand(v_1.mul(v_2)))));
						log_part = log_part.add(y_1.mul(log_to_arctan(A_1, B_1, x)));
						i = i + 2;
						continue;
					}
				}
				log_part = log_part.add(c_1.mul(new Expr(Operator.LOG, v_1)));
				i = i + 1; 
			}
			if(i-1 < log.length)
				log_part = log_part.add(log[i-1][0].mul(new Expr(Operator.LOG, log[i-1][1])));
			return log_part.add(gh[0].add(integrate_poly(qr[0], x)));
		}
	}
	
	/**
	 * Integration of a polynomial in Q[x]
	 * @param u - a polynomial in Q[x]
	 * @param x - a variable
	 * @return the function g, such that diff(g, x) = u.
	 */
	public static Expr integrate_poly(Expr u, Expr x)
	{
		if(u.equals(Int.ZERO))
			return Int.ZERO;
		Int n = Poly.degree(u, x);
		Expr sum = Int.ZERO;
		for(Int i = Int.ZERO;i.compareTo(n)<=0;i = i.add(Int.ONE))
		{
			Expr c = Poly.coefficient_poly(u, x, i);
			sum = sum.add(c.div(i.add(Int.ONE)).mul(x.pow(i.add(Int.ONE))));
		}
		return sum;
	}

	/**
	 * Hermite Reduction in Q(x)
	 * @param p - a polynomial in Q[x]
	 * @param q - a polynomial in Q[x]
	 * @param x - a variable
	 * @return the list [g, h] such that diff(g, x) + h = p/q and h has a square-free denominator.
	 */
	public static Expr[] hermite_reduction(Expr p, Expr q, Expr x)
	{
		Expr g = Int.ZERO;
		Expr[] D = Factor.square_free_factorization_rationals(q, new Expr[]{x});
		int m = D.length;
		for(int i = 2;i <= m;i++)
		{
			if(Poly.degree(D[i-1], x).compareTo(Int.ZERO) > 0)
			{
				Expr V = D[i-1];
				Expr U = BasicPoly.polynomial_quotient(q, Algebra.expand(V.pow(new Int(i))), x);
				for(int j = i-1;j>=1;j--)
				{
					Expr t = Algebra.expand(U.mul(Diff.derivative(V, x)));
					Expr r = p.div(new Int(-j));
					Expr[] BC = GCD.solve(t, V, r, x);
					Expr B = BC[0], C = BC[1];
					g = Algebra.cancel(g.add(B.div(V.pow(new Int(j)))));
					p = Algebra.expand(new Int(-j).mul(C).sub(U.mul(Diff.derivative(B, x))));
				}
				q = Algebra.expand(U.mul(V));
			}
		}
		return new Expr[]{g, Algebra.cancel(p.div(q))};
	}
	
	/**
	 * The logarithmic part of the integral using Rothstein-Trager method
	 * @param a - a polynomial in Q[x] with deg(a) < deg(b) and gcd(a, b) = 1
	 * @param b - a polynomial in Q[x] such that gcd(b, diff(b, x)) = 1
	 * @param x - a variable
	 * @return the list [[c_1, v_1], ..., [c_k, v_k]] such that <br>
	 * a/b = sum(c_i*diff(v_i, x)/v_i, i, 1, k)
	 */
	public static Expr[][] logarithmic_part(Expr a, Expr b, Expr x)
	{
		Expr z = Simplification.getNewVariables(1, a, b, x)[0];
		Expr b_prime = Diff.derivative(b, x);
		Expr R = GCD.primitive(Resultant.multivariate_resultant(Algebra.expand(a.sub(z.mul(b_prime))), b, new Expr[]{x, z}, "Q"), z, new  Expr[]{}, "Q");
		Expr[] r = Factor.factor_poly_rationals_distinct(R, z);
		Expr[][] integral = new Expr[][]{};
		for(int i = 0;i<r.length;i++)
		{
			Int d = Poly.degree(r[i], z);
			if(d.compareTo(Int.ONE) < 0)
				continue;
			if(d.equals(Int.ONE))
			{
				Expr c = Int.NONE.mul(Poly.coefficient_poly(r[i], z, Int.ZERO)).div(Poly.coefficient_poly(r[i], z, Int.ONE));
				Expr v = GCD.multivariate_gcd(Algebra.expand(a.sub(c.mul(b_prime))), b, new Expr[]{x}, "Q");
				v = BasicPoly.make_monic(v, x);
				integral = Set.add(integral, new Expr[][]{{c, v}});
			}
			else
			{
				Expr alpha = Simplification.getNewVariables(1, a, b, x, z)[0];
				Expr p = r[i].substitute(z, alpha);
				Expr v = GCDAlgebraicNumberField.polynomial_gcd(Algebra.expand(a.sub(alpha.mul(b_prime))), b, x, new Expr[]{p}, new Expr[]{alpha});
				v = AlgebraicNumberField.make_monic(v, x, new Expr[]{p}, new Expr[]{alpha});
				if(d.equals(Int.TWO))
				{
				    Expr ca = Poly.coefficient_poly(p, alpha, Int.TWO);	
				    Expr cb = Poly.coefficient_poly(p, alpha, Int.ONE);	
				    Expr cc = Poly.coefficient_poly(p, alpha, Int.ZERO);
				    Expr c_1 = Int.NONE.mul(cb).add(cb.mul(cb).sub(Int.FOUR.mul(ca.mul(cc))).pow(Rational.HALF)).div(Int.TWO.mul(ca));
				    Expr c_2 = Int.NONE.mul(cb).sub(cb.mul(cb).sub(Int.FOUR.mul(ca.mul(cc))).pow(Rational.HALF)).div(Int.TWO.mul(ca));
				    integral = Set.add(integral, new Expr[][]{{c_1, Simplification.simplify_recursive(v.substitute(alpha, c_1))},{c_2, Simplification.simplify_recursive(v.substitute(alpha, c_2))}});
				}
				else
				{
					for(Int j = Int.ZERO;j.compareTo(d)<0;j = j.add(Int.ONE))
					{
						Expr c = new Expr(Operator.ROOTOF, p, alpha, j.add(Int.ONE));
						integral = Set.add(integral, new Expr[][]{{c, Simplification.simplify_recursive(v.substitute(alpha, c))}});
					}
				}
			}
		}
		return integral;
	}
	
	/**
	 * The logarithmic part of the integral using Lazard-Rioboo improvement
	 * @param a - a polynomial in Q[x] with deg(a) < deg(b) and gcd(a, b) = 1
	 * @param b - a polynomial in Q[x] such that gcd(b, diff(b, x)) = 1
	 * @param x - a variable
	 * @return the list [[c_1, v_1], ..., [c_k, v_k]] such that <br>
	 * a/b = sum(c_i*diff(v_i, x)/v_i, i, 1, k)
	 */
	public static Expr[][] logarithmic_part_lazard_rioboo(Expr a, Expr b, Expr x)
	{
		Expr t = Simplification.getNewVariables(1, a, b, x)[0];
		Expr[][] R = Resultant.subresultant_sequence(b, Algebra.expand(a.sub(t.mul(Diff.derivative(b, x)))), new Expr[]{x, t}, "Q");
		Expr[] Q = Factor.square_free_factorization_rationals(R[0][0], t);
		Expr[] S = new Expr[Q.length];
		for(int i = 1;i<=Q.length;i++)
		{
			if(Poly.degree(Q[i-1], t).compareTo(Int.ZERO) > 0)
			{
				if(Poly.degree(b, x).equals(new Int(i)))
					S[i-1] = b;
				else
				{
					for(int j = 0;j<R[1].length;j++)
					{
						if(Poly.degree(R[1][j], x).equals(new Int(i)))
						{
							S[i-1] = R[1][j];
							break;
						}
					}
					Expr[] A = Factor.square_free_factorization_rationals(Poly.leading_coef(S[i-1], x), new Expr[]{t});
					for(int j = 1;j<=A.length;j++)
						S[i-1] = BasicPoly.polynomial_quotient(S[i-1], Algebra.expand(GCD.multivariate_gcd(A[j-1], Q[i-1], "Q").pow(new Int(j))), x);
				}
			}
			else
			{
				for(int j = 0;j<R[1].length;j++)
				{
					if(Poly.degree(R[1][j], x).equals(new Int(i)))
					{
						S[i-1] = R[1][j];
						break;
					}
				}
			}
		}
		Expr[][] log = new Expr[][]{};
		for(int i = 1;i<=Q.length;i++)
		{
			Expr[] s = PolySolve.solve_polynomial(Q[i-1], t);
			//make log arguments monic
			S[i-1] = AlgebraicNumberField.make_monic(S[i-1], x, new Expr[]{Q[i-1]}, new Expr[]{t});
			for(int j = 0;j<s.length;j++)
				log = Set.add(log, new Expr[][]{{s[j], Algebra.expand(Simplification.simplify_recursive(S[i-1].substitute(t, s[j])))}});
		}
		return log;
	}
	
	/**
	 * Converts complex logarithms to real arctangents with polynomial arguments
	 * @param A - a polynomial in Q[x]
	 * @param B - a polynomial in Q[x] such that B != 0
	 * @param x - a variable
	 * @return the function g such that diff(g, x) = diff(i*log((A+I*B)/(A-I*B)), x)
	 */
	public static Expr log_to_arctan(Expr A, Expr B, Expr x)
	{
		Expr[] qr = BasicPoly.polynomial_division(A, B, x);
		if(qr[1].equals(Int.ZERO))
		{
			if(qr[0].isFreeOf(x))
				return Int.ZERO;
			return Int.TWO.mul(new Expr(Operator.ARCTAN, qr[0]));
		}
		if(Poly.degree(A, x).compareTo(Poly.degree(B, x)) < 0)
			return log_to_arctan(B.mul(Int.NONE), A, x);
		Expr[] DCG = GCD.polynomial_extended_gcd(B, A.mul(Int.NONE), x);
		Expr D = DCG[1], C = DCG[2], G = DCG[0];
		Expr F = log_to_arctan(D, C, x);
		Expr P = BasicPoly.polynomial_quotient(Algebra.expand(A.mul(D).add(B.mul(C))), G, x);
		return Int.TWO.mul(new Expr(Operator.ARCTAN, P)).add(F);
	}
	
}
