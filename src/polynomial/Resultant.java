package polynomial;

import java.util.Vector;

import algebra.Algebra;
import Expression.Expr;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;

public class Resultant 
{
	
	static Constant DEFAULT_RESULTANT = Constant.MODULAR;
	
	public static Expr multivariate_resultant(Expr u, Expr v, Expr x, String K)
	{
		Expr[] vars = Set.add(new Expr[]{x}, Set.complement(Set.union(Poly.variables(u), Poly.variables(v)), new Expr[]{x}));
		Expr[] subs = Simplification.getNewVariables(vars.length, u, v, x);
		u = Algebra.expand(u.substitute(vars, subs));
		v = Algebra.expand(v.substitute(vars, subs));
		Expr res = multivariate_resultant(u, v, subs, K);
		return Simplification.simplify_recursive(res.substitute(subs, vars));
	}
	
	public static Expr[] multivariate_subresultant(Expr u, Expr v, Expr x, String K)
	{
		Expr[] vars = Set.add(new Expr[]{x}, Set.complement(Set.union(Poly.variables(u), Poly.variables(v)), new Expr[]{x}));
		Expr[] subs = Simplification.getNewVariables(vars.length, u, v, x);
		u = Algebra.expand(u.substitute(vars, subs));
		v = Algebra.expand(v.substitute(vars, subs));
		Expr[] res = subresultant_sequence(u, v, subs, K)[1];
		Expr[] r = new Expr[res.length];
		for(int i = 0;i<res.length;i++)
			r[i] = Simplification.simplify_recursive(res[i].substitute(subs, vars));
		return r;
	}
	
	public static Expr multivariate_resultant(Expr u, Expr v, Expr[] L, String K)
	{
		return multivariate_resultant(u, v, L, K, DEFAULT_RESULTANT);
	}

	public static Expr multivariate_resultant(Expr u, Expr v, Expr[] L, String K, Constant c)
	{
		if(K.equals("Z"))
		{
			if(c.equals(Constant.EUCLID))
				return resultant(u, v, L, "Z");
			if(c.equals(Constant.MODULAR))
				return modular_resultant_integers(u, v, L);
			if(c.equals(Constant.SUBRESULTANT))
				return subresultant_sequence(u, v, L, K)[0][0];
		}
		else
		{
			if(c.equals(Constant.EUCLID))
				return resultant(u, v, L, "Q");
			if(c.equals(Constant.MODULAR))
				return modular_resultant_rationals(u, v, L);
			if(c.equals(Constant.SUBRESULTANT))
				return subresultant_sequence(u, v, L, K)[0][0];
		}
		return null;
	}

	public static Expr resultant(Expr u, Expr v, Expr x)
	{
		Int m = Poly.degree(u, x);
		Int n = Poly.degree(v, x);
		if(n.equals(Int.ZERO))
			return v.pow(m);
		else
		{
			Expr r = BasicPoly.polynomial_remainder(u, v, x);
			if(r.equals(Int.ZERO))
				return Int.ZERO;
			else
			{
				Expr s = Poly.degree(r, x);
				Expr l = Poly.coefficient_poly(v, x, n);
				return Algebra.expand(Int.NONE.pow(n.mul(m)).mul(l.pow(m.sub(s))).mul(resultant(v, r, x)));
			}
		}
	}

	public static Expr resultant_p(Expr u, Expr v, Expr x, Int p)
	{
		Int m = Poly.degree(u, x);
		Int n = Poly.degree(v, x);
		if(n.equals(Int.ZERO))
			return v.pow(m);
		else
		{
			Expr r = BasicPoly.polynomial_remainder_p(u, v, x, p);
			if(r.equals(Int.ZERO))
				return Int.ZERO;
			else
			{
				Expr s = Poly.degree(r, x);
				Expr l = Poly.coefficient_poly(v, x, n);
				return FiniteField.to_non_negative(Algebra.expand(Int.NONE.pow(n.mul(m)).mul(l.pow(m.sub(s))).mul(resultant_p(v, r, x, p))), p);
			}
		}
	}

	public static Expr resultant(Expr u, Expr v, Expr[] L, String K)
	{
		Expr x = L[0];
		Int m = Poly.degree(u, x);
		Int n = Poly.degree(v, x);
		if(m.compareTo(n)<0)
			return Int.NONE.pow(m.mul(n)).mul(resultant(v, u, L, K));
		if(n.equals(Int.ZERO))
			return v.pow(m);
		Int delta = m.sub(n).add(Int.ONE);
		Expr r = BasicPoly.pseudo_division(u, v, x)[1];
		if(r.equals(Int.ZERO))
			return Int.ZERO;
		Int s = Poly.degree(r, x);
		Expr l = Poly.coefficient_poly(v, x, n);
		Expr w = Algebra.expand(Int.NONE.pow(m.mul(n)).mul(resultant(v, r, L, K)));
		Int k = delta.mul(n).sub(m).add(s);
		Expr f = Algebra.expand(l.pow(k));
		return BasicPoly.multivariate_division(w, f, L, K)[0];
	}

	public static Expr modular_resultant_rationals(Expr u, Expr v, Expr[] L)
	{
		Int a = Poly.coefficient_lcm(u, L);
		Int b = Poly.coefficient_lcm(v, L);
		u = u.mul(a);
		v = v.mul(b);
		Int m = Poly.degree(u, L[0]);
		Int n = Poly.degree(v, L[0]);
		Expr gcd = modular_resultant_integers(u, v, L);
		return gcd.div(a.pow(n).mul(b.pow(m)));
	}

	public static Expr modular_resultant_integers(Expr u, Expr v, Expr[] L)
	{
		Int a = (Int) Poly.leading_coef(u, L);
		Int b = (Int) Poly.leading_coef(v, L);
		Int g = Int.gcd(a, b);
		Int limit = resultant_bound(u, v, L);
		Int p_k = new Int("170141183460469231731687303715884105728");
		Expr H = null;
		Int q = Int.ONE;
		while(true)
		{
			Int p = Int.find_prime(p_k);
			while(g.mod(p).isZero())
				p = Int.find_prime(p.add(Int.ONE));
			p_k = p.add(Int.ONE);
			Expr u_p = FiniteField.to_symmetric(u, p);
			Expr v_p = FiniteField.to_symmetric(v, p);
			Expr res = multivariate_modular_resultant(u_p, v_p, L, p);
			if(H == null)
				H = res;
			else
			{
				H = FiniteField.integer_chinese_remainder_garner(new Expr[]{H, res}, new Int[]{q, p});
			}
			q = q.mul(p);
			if(q.compareTo(limit)>0)
				return H;
		}
	}

	public static Expr multivariate_modular_resultant(Expr u, Expr v, Expr[] L, Int p) 
	{
		if(L.length == 1)
			return FiniteField.to_symmetric(resultant_p(u, v, L[0], p), p);
		Expr x = L[0];
		Expr y = L[L.length-1];
		Expr[] R = new Expr[L.length-1];
		for(int i = 0;i<R.length;i++)
			R[i] = L[i];
		Int n = Poly.degree(u, x);
		Int m = Poly.degree(v, x);
		Int degree_limit = Poly.degree(u, y).mul(m).add(Poly.degree(v, y).mul(n));
		if(degree_limit.compareTo(p) > 0)
			return null;
		Expr g_u = Poly.leading_coef(u, R);
		Expr g_v = Poly.leading_coef(v, R);
		Vector<Int> b_p = new Vector<>();
		Vector<Expr> C_b_p = new Vector<>();
		while(true)
		{
			Int b = null;
			do
			{
				b = Int.random_int(Int.ZERO, p);
			}
			while(Simplification.simplify_recursive(FiniteField.to_symmetric(Poly.horner_evaluate(g_u, y, b), p)).equals(Int.ZERO)
					|| FiniteField.to_symmetric(Poly.horner_evaluate(g_v, y, b), p).equals(Int.ZERO) || Set.is_in_vector(b_p, b));
			Expr u_b = FiniteField.to_symmetric(Poly.horner_evaluate(u, y, b), p);
			Expr v_b = FiniteField.to_symmetric(Poly.horner_evaluate(v, y, b), p);
			Expr res = multivariate_modular_resultant(u_b, v_b, R, p);
			b_p.add(b);
			C_b_p.add(res);
			if(b_p.size() > degree_limit.toInt())
			{ 	
				Expr H = FiniteField.newton_interpolation(b_p.toArray(new Int[b_p.size()]), C_b_p.toArray(new Expr[C_b_p.size()]), y, p);
				return H;
			}
		}
	}

	private static Int resultant_bound(Expr u, Expr v, Expr[] L) 
	{
		Expr x = L[0];
		Expr[] R = new Expr[L.length-1];
		for(int i = 0;i<R.length;i++)
			R[i] = L[i+1];

		Int m = Poly.degree(u, x);
		Int n = Poly.degree(v, x);

		Int A = Int.ZERO;
		for(Int i = Int.ZERO;i.compareTo(m)<=0;i = i.add(Int.ONE))
		{
			Int j = Poly.plus_norm(Poly.coefficient_poly(u, x, i), R);
			A = j.compareTo(A)>0?j:A;
		}

		Int B = Int.ZERO;
		for(Int i = Int.ZERO;i.compareTo(n)<=0;i = i.add(Int.ONE))
		{
			Int j = Poly.plus_norm(Poly.coefficient_poly(v, x, i), R);
			B = j.compareTo(B)>0?j:B;
		}
		return (Int)m.add(n).factorial().mul(A.pow(n).mul(B.pow(m)));
	}
	
	public static Expr[][] subresultant_sequence(Expr A, Expr B, Expr[] vars, String K)
	{
		Expr x = vars[0];
		Vector<Expr> R = new Vector<>();
		R.add(A);
		R.add(B);
		int i = 1;
		Vector<Expr> gamma = new Vector<>();
		gamma.add(Int.NONE);
		Vector<Int> delta = new Vector<>();
		delta.add(Poly.degree(A, x).sub(Poly.degree(B, x)));
		Vector<Expr> beta = new Vector<>();
		beta.add(Int.NONE.pow(delta.get((i)-1).add(Int.ONE)));
		Vector<Expr> r = new Vector<>();
		while(!R.get(i).equals(Int.ZERO))
		{
			r.add(Poly.coefficient_poly(R.get(i), x, Poly.degree(R.get(i), x)));
			Expr[] QR = BasicPoly.pseudo_division(R.get(i-1), R.get(i), x);
			R.add(BasicPoly.multivariate_division(QR[1], beta.get((i)-1), vars, K)[0]);
			i = i+1;
			gamma.add(Algebra.expand(Algebra.cancel(Int.NONE.mul(r.get((i-1)-1)).pow(delta.get((i-1)-1)).mul(gamma.get((i-1)-1).pow(Int.ONE.sub(delta.get((i-1)-1)))))));
		    delta.add(Poly.degree(R.get(i-1), x).sub(Poly.degree(R.get(i),x)));
		    beta.add(Algebra.expand(Algebra.cancel(Int.NONE.mul(r.get((i-1)-1)).mul(gamma.get((i)-1).pow(delta.get((i)-1))))));
		}
		int k = i-1;
		if(Poly.degree(R.get(k), x).compareTo(Int.ZERO)>0)
		{
			return new Expr[][]{{Int.ZERO}, R.toArray(new Expr[R.size()])};
		}
		if(Poly.degree(R.get(k-1), x).equals(Int.ONE))
		{
			return new Expr[][]{{R.get(k)}, R.toArray(new Expr[R.size()])};
		}
		Expr s = Int.ONE;
		Expr c = Int.ONE;
		for(int j = 1;j<=k-1;j++)
		{
			if(Poly.degree(R.get(j-1), x).isOdd() && Poly.degree(R.get(j), x).isOdd())
				s = s.mul(Int.NONE);
			c = c.mul(BasicPoly.multivariate_division(beta.get((j)-1),r.get((j)-1), vars, K)[0].pow(Int.ONE.add(delta.get((j)-1)))).pow(Poly.degree(R.get(j), x)).mul(r.get((j)-1).pow(Poly.degree(R.get(j-1), x).sub(Poly.degree(R.get(j+1), x))));
		}
		return new Expr[][]{{Algebra.expand(s.mul(c.mul(R.get(k).pow(Poly.degree(R.get(k-1), x)))))}, (R.toArray(new Expr[R.size()]))};
	}

}
