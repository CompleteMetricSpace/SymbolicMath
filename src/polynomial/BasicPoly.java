package polynomial;

import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;
import Symbolic.Rational;
import algebra.Algebra;
import Expression.Expr;
import Expression.Operator;

public class BasicPoly
{

    public static Expr[] multivariate_division(Expr u, Expr v, Expr[] L, String K)
    {
	u = Algebra.expand(u);
	v = Algebra.expand(v);
	if(L.length == 0)
	{
	    Expr f = (u.div(v));
	    if(K.equals("Z"))
	    {
		if(u.isInt() && v.isInt())
		{
		    if(f.isInt())
			return new Expr[] {f, Int.ZERO};
		    else
			return new Expr[] {Int.ZERO, u};
		}
		else
		    return new Expr[] {f, Int.ZERO};
	    }
	    else
		return new Expr[] {f, Int.ZERO};
	}
	else
	{
	    Expr x = L[0];
	    Expr[] rest = new Expr[L.length - 1];
	    for(int i = 0; i < rest.length; i++)
		rest[i] = L[i + 1];
	    Expr r = u;
	    Int m = Poly.degree(u, x);
	    Int n = Poly.degree(v, x);
	    Expr q = Int.ZERO;
	    Expr lcv = Poly.coefficient_poly(v, x, n);
	    while(m.compareTo(n) >= 0)
	    {
		Expr lcr = Poly.coefficient_poly(r, x, Poly.degree(r, x));
		Expr[] d = multivariate_division(lcr, lcv, rest, K);
		if(!d[1].equals(Int.ZERO))
		    return new Expr[] {Algebra.expand(q), r};
		else
		{
		    Expr c = d[0];
		    if(!m.equals(Int.NONE))
		    {
			q = Algebra.expand(q.add(c.mul(x.pow(m.sub(n)))));
			r = Algebra.expand(r.sub(c.mul(v).mul(x.pow(m.sub(n)))));
		    }
		    m = Poly.degree(r, x);
		}
	    }
	    return new Expr[] {q, r};
	}
    }

    public static Expr[] multivariate_division_p(Expr u, Expr v, Expr[] L, Int p)
    {
	u = FiniteField.to_non_negative(Algebra.expand(u), p);
	v = FiniteField.to_non_negative(Algebra.expand(v), p);
	if(L.length == 0)
	{
	    Int V = (Int) v;
	    Int U = (Int) u;
	    return new Expr[] {U.mul(V.modInverse(p)).mod(p), Int.ZERO};
	}
	else
	{
	    Expr x = L[0];
	    Expr[] rest = new Expr[L.length - 1];
	    for(int i = 0; i < rest.length; i++)
		rest[i] = L[i + 1];
	    Expr r = u;
	    Int m = Poly.degree(u, x);
	    Int n = Poly.degree(v, x);
	    Expr q = Int.ZERO;
	    Expr lcv = Poly.coefficient_poly(v, x, n);
	    while(m.compareTo(n) >= 0)
	    {
		Expr lcr = Poly.coefficient_poly(r, x, Poly.degree(r, x));
		Expr[] d = multivariate_division_p(lcr, lcv, rest, p);
		if(!d[1].equals(Int.ZERO))
		    return new Expr[] {q, r};
		else
		{
		    Expr c = d[0];
		    if(!m.equals(Int.NONE))
		    {
			q = FiniteField.to_non_negative(
				Algebra.expand(q.add(c.mul(x.pow(m.sub(n))))), p);
			r = FiniteField.to_non_negative(
				Algebra.expand(r.sub(c.mul(v).mul(x.pow(m.sub(n))))), p);
		    }
		    m = Poly.degree(r, x);
		}
	    }
	    q = FiniteField.to_non_negative(q, p);
	    r = FiniteField.to_non_negative(r, p);
	    return new Expr[] {q, r};
	}
    }

    public static Expr[] polynomial_division(Expr u, Expr v, Expr x)
    {
	Expr q = Int.ZERO;
	Expr r = u;
	Int m = Poly.degree(r, x);
	Int n = Poly.degree(v, x);
	Expr lcv = Poly.coefficient_poly(v, x, n);
	while(m.compareTo(n) >= 0)
	{
	    Expr lcr = Poly.leading_coef(r, x);
	    Expr s = lcr.div(lcv);
	    q = q.add(s.mul(x.pow(m.sub(n))));
	    r = Algebra.expand(r.sub(lcr.mul(x.pow(m))).sub(
		    v.sub(lcv.mul(x.pow(n))).mul(s).mul(x.pow(m.sub(n)))));
	    m = Poly.degree(r, x);
	}
	return new Expr[] {q, r};
    }

    public static Expr polynomial_remainder(Expr u, Expr v, Expr x)
    {
	return polynomial_division(u, v, x)[1];
    }

    public static Expr polynomial_quotient(Expr u, Expr v, Expr x)
    {
	return polynomial_division(u, v, x)[0];
    }

    public static Expr[] polynomial_division_Q(Expr u, Expr v, Expr x)
    {
	Expr q = Int.ZERO;
	Expr r = u;
	Int m = Poly.degree(r, x);
	Int n = Poly.degree(v, x);
	Expr lcv = Poly.coefficient_poly(v, x, n);
	while(m.compareTo(n) >= 0)
	{
	    Expr lcr = Poly.leading_coef_Q(r, x);
	    Expr s = lcr.div(lcv);
	    q = q.add(s.mul(x.pow(m.sub(n))));
	    r = Algebra.expand(r.sub(lcr.mul(x.pow(m))).sub(
		    v.sub(lcv.mul(x.pow(n))).mul(s).mul(x.pow(m.sub(n)))));
	    m = Poly.degree(r, x);
	}
	return new Expr[] {q, r};
    }

    public static Expr[] polynomial_division_p(Expr u, Expr v, Expr x, Int p)
    {
	u = FiniteField.to_non_negative(u, p);
	v = FiniteField.to_non_negative(v, p);
	Expr q = Int.ZERO;
	Expr r = u;
	Int m = Poly.degree(r, x);
	Int n = Poly.degree(v, x);
	Int lcv = (Int) Poly.coefficient_poly(v, x, n);
	while(m.compareTo(n) >= 0)
	{
	    Expr lcr = (Int) Poly.leading_coef_Q(r, x);
	    Expr s = lcr.mul(lcv.modInverse(p));
	    q = q.add(s.mul(x.pow(m.sub(n))));
	    r = Algebra.expand(r.sub(lcr.mul(x.pow(m))).sub(
		    v.sub(lcv.mul(x.pow(n))).mul(s).mul(x.pow(m.sub(n)))));
	    q = FiniteField.to_non_negative(q, p);
	    r = FiniteField.to_non_negative(r, p);
	    m = Poly.degree(r, x);
	}
	return new Expr[] {q, r};
    }

    public static Expr polynomial_remainder_p(Expr u, Expr v, Expr x, Int p)
    {
	return polynomial_division_p(u, v, x, p)[1];
    }

    public static Expr polynomial_quotient_p(Expr u, Expr v, Expr x, Int p)
    {
	return polynomial_division_p(u, v, x, p)[0];
    }

    public static Expr polynomial_expansion(Expr u, Expr v, Expr x, Expr t)
    {
	if(u.equals(Int.ZERO))
	    return Int.ZERO;
	Expr[] d = polynomial_division(u, v, x);
	Expr q = d[0];
	Expr r = d[1];
	return Algebra.expand(t.mul(polynomial_expansion(q, v, x, t)).add(r));
    }

    public static Expr make_monic(Expr u, Expr x)
    {
	Expr lc = Poly.leading_coef(u, x);
	return Algebra.expand(u.div(lc));
    }

    public static Expr make_monic_cancel(Expr u, Expr x)
    {
	Expr lc = Poly.leading_coef(u, x);
	return Algebra.expand(Algebra.cancel(u.div(lc)));
    }

    public static Expr lagrange_polynomial(Expr[][] points, Expr x)
    {
	int r = points.length;
	Expr sum = Int.ZERO;
	for(int i = 0; i < r; i++)
	{
	    Expr[] list = new Expr[points.length];
	    for(int j = 0; j < list.length; j++)
		list[j] = points[j][0];
	    sum = sum.add(lagrange_p_i(list, i, x).mul(points[i][1]));
	}
	return Algebra.expand(sum);
    }

    private static Expr lagrange_p_i(Expr[] t, int i, Expr x)
    {
	Expr num = Int.ONE;
	for(int j = 0; j < t.length; j++)
	{
	    if(j != i)
		num = num.mul(x.sub(t[j]));
	}
	Expr denom = Int.ONE;
	for(int j = 0; j < t.length; j++)
	{
	    if(j != i)
		denom = denom.mul(t[i].sub(t[j]));
	}
	return Algebra.expand(num.div(denom));
    }

    public static Expr[] pseudo_division(Expr u, Expr v, Expr x)
    {
	Expr p = Int.ZERO;
	Expr s = u;
	Int m = Poly.degree(s, x);
	Int n = Poly.degree(v, x);
	Int delta = Int.max(m.sub(n).add(Int.ONE), Int.ZERO);
	Expr lcv = Poly.coefficient_poly(v, x, n);
	Int sigma = Int.ZERO;
	while(m.compareTo(n) >= 0)
	{
	    Expr lcs = Poly.coefficient_poly(s, x, m);
	    p = lcv.mul(p).add(lcs.mul(x.pow(m.sub(n))));
	    s = Algebra.expand(lcv.mul(s).sub(lcs.mul(v).mul(x.pow(m.sub(n)))));
	    sigma = sigma.add(Int.ONE);
	    m = Poly.degree(s, x);
	}
	return new Expr[] {Algebra.expand(lcv.pow(delta.sub(sigma)).mul(p)),
		Algebra.expand(lcv.pow(delta.sub(sigma)).mul(s))};
    }

    public static Expr cyclotomic_polynomial(Expr x, Int n)
    {
	if(n.equals(Int.ONE))
	    return x.sub(Int.ONE);
	if(n.isPrime())
	{
	    Expr sum = Int.ZERO;
	    for(Int i = Int.ZERO; i.compareTo(n) < 0; i = i.add(Int.ONE))
		sum = sum.add(x.pow(i));
	    return sum;
	}
	if(!n.isOdd() && n.divide(Int.TWO).isOdd())
	{
	    Expr cyc = cyclotomic_polynomial(x, n.divide(Int.TWO));
	    return Simplification.simplify_recursive(cyc.substitute(x, x.mul(Int.NONE)));
	}
	for(Int p = Int.TWO; p.compareTo(n) < 0; p = p.add(Int.ONE))
	{
	    if(n.mod(p).equals(Int.ZERO))
	    {
		Int i = n.divide(p);
		// p is prime
		if(Int.gcd(p, i).equals(Int.ONE))
		{
		    Expr cyc = cyclotomic_polynomial(x, i);
		    Expr cycp = Simplification.simplify_recursive(cyc.substitute(x, x.pow(p)));
		    return BasicPoly.polynomial_quotient(cycp, cyc, x);
		}
		else
		{
		    Expr cyc = cyclotomic_polynomial(x, i);
		    Expr cycp = Simplification.simplify_recursive(cyc.substitute(x, x.pow(p)));
		    return cycp;
		}
	    }
	}
	// Not possible
	return null;
    }

    public static Expr swinnerton_dyer_polynomial(Expr x, Int n)
    {
	if(n.equals(Int.ONE))
	    return x.pow(Int.TWO).sub(Int.TWO);
	Expr sdp = swinnerton_dyer_polynomial(x, n.sub(Int.ONE));
	Int p = Int.nth_prime(n);
	Expr s1 = Algebra.expand(Simplification.simplify_recursive(sdp.substitute(x,
		x.add(p.pow(Rational.HALF)))));
	Expr s2 = Algebra.expand(Simplification.simplify_recursive(sdp.substitute(x,
		x.sub(p.pow(Rational.HALF)))));
	return Algebra.expand(s1.mul(s2));
    }

}
