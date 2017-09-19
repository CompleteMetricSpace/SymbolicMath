package polynomial;

import java.util.Vector;

import algebra.Algebra;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;
import Symbolic.Numerical;
import Symbolic.Rational;

public class Poly
{
    public static boolean is_monomial(Expr u, Expr... x)
    {
	if(Set.member(x, u))
	    return true;
	if(u.isPower())
	{
	    Expr b = u.get(0);
	    Expr e = u.get(1);
	    if(Set.member(x, b) && e.isInt() && ((Int) e).compareTo(Int.ONE) > 0)
		return true;
	}
	if(u.isProduct())
	{
	    for(int i = 0; i < u.length(); i++)
		if(!is_monomial(u.get(i), x))
		    return false;
	    return true;
	}
	return u.isFreeOf(x);
    }

    public static boolean is_monomial_gie(Expr u, Expr... x)
    {
	if(Set.member(x, u))
	    return true;
	if(u.isPower())
	{
	    Expr b = u.get(0);
	    Expr e = u.get(1);
	    if(Set.member(x, b) && e.isInt())
		return true;
	}
	if(u.isProduct())
	{
	    for(int i = 0; i < u.length(); i++)
		if(!is_monomial_gie(u.get(i), x))
		    return false;
	    return true;
	}
	return u.isFreeOf(x);
    }

    public static boolean is_monomial_Q(Expr u, Expr... x)
    {
	if(Set.member(x, u))
	    return true;
	if(u.isPower())
	{
	    Expr b = u.get(0);
	    Expr e = u.get(1);
	    if(Set.member(x, b) && e.isInt() && ((Int) e).compareTo(Int.ONE) > 0)
		return true;
	}
	if(u.isProduct())
	{
	    for(int i = 0; i < u.length(); i++)
		if(!is_monomial_Q(u.get(i), x))
		    return false;
	    return true;
	}
	return u.isNumerical();
    }

    public static boolean is_monomial_Z(Expr u, Expr... x)
    {
	if(Set.member(x, u))
	    return true;
	if(u.isPower())
	{
	    Expr b = u.get(0);
	    Expr e = u.get(1);
	    if(Set.member(x, b) && e.isInt() && ((Int) e).compareTo(Int.ONE) > 0)
		return true;
	}
	if(u.isProduct())
	{
	    for(int i = 0; i < u.length(); i++)
		if(!is_monomial_Z(u.get(i), x))
		    return false;
	    return true;
	}
	return u.isInt();
    }

    public static boolean is_poly(Expr u, Expr... x)
    {
	if(!u.isSum())
	    return is_monomial(u, x);
	else
	{
	    if(Set.member(x, u))
		return true;
	    for(int i = 0; i < u.length(); i++)
		if(!is_monomial(u.get(i), x))
		    return false;
	    return true;
	}
    }

    public static boolean is_poly_gie(Expr u, Expr... x)
    {
	if(!u.isSum())
	    return is_monomial_gie(u, x);
	else
	{
	    if(Set.member(x, u))
		return true;
	    for(int i = 0; i < u.length(); i++)
		if(!is_monomial_gie(u.get(i), x))
		    return false;
	    return true;
	}
    }

    public static boolean is_poly_Q(Expr u, Expr... x)
    {
	if(!u.isSum())
	    return is_monomial_Q(u, x);
	else
	{
	    if(Set.member(x, u))
		return true;
	    for(int i = 0; i < u.length(); i++)
		if(!is_monomial_Q(u.get(i), x))
		    return false;
	    return true;
	}
    }

    public static boolean is_poly_Z(Expr u, Expr... x)
    {
	if(!u.isSum())
	    return is_monomial_Z(u, x);
	else
	{
	    if(Set.member(x, u))
		return true;
	    for(int i = 0; i < u.length(); i++)
		if(!is_monomial_Z(u.get(i), x))
		    return false;
	    return true;
	}
    }

    public static Expr[] coefficient_monomial(Expr u, Expr x)
    {
	if(u.equals(x))
	    return new Expr[] {Int.ONE, Int.ONE};
	if(u.isPower())
	{
	    Expr base = u.get(0);
	    Expr exponent = u.get(1);
	    if(base.equals(x) && exponent.isInt() && ((Int) exponent).isPositive())
		return new Expr[] {Int.ONE, exponent};
	}
	if(u.isProduct())
	{
	    Expr c = u;
	    Int m = Int.ZERO;
	    for(int i = 0; i < u.length(); i++)
	    {
		Expr[] f = coefficient_monomial(u.get(i), x);
		if(f == null)
		    return null;
		if(!f[1].equals(Int.ZERO))
		{
		    m = (Int) f[1];
		    c = u.div(x.pow(m));
		}
	    }
	    return new Expr[] {c, m};
	}
	if(u.isFreeOf(x))
	    return new Expr[] {u, Int.ZERO};
	return null;
    }

    public static Expr[] coefficient_monomial_gie(Expr u, Expr x)
    {
	if(u.equals(x))
	    return new Expr[] {Int.ONE, Int.ONE};
	if(u.isPower())
	{
	    Expr base = u.get(0);
	    Expr exponent = u.get(1);
	    if(base.equals(x) && exponent.isInt())
		return new Expr[] {Int.ONE, exponent};
	}
	if(u.isProduct())
	{
	    Expr c = u;
	    Int m = Int.ZERO;
	    for(int i = 0; i < u.length(); i++)
	    {
		Expr[] f = coefficient_monomial_gie(u.get(i), x);
		if(f == null)
		    return null;
		if(!f[1].equals(Int.ZERO))
		{
		    m = (Int) f[1];
		    c = u.div(x.pow(m));
		}
	    }
	    return new Expr[] {c, m};
	}
	if(u.isFreeOf(x))
	    return new Expr[] {u, Int.ZERO};
	return null;
    }

    public static Expr[][] coefficient_monomial(Expr u, Expr[] x)
    {
	for(int i = 0; i < x.length; i++)
	{
	    if(u.equals(x[i]))
		return new Expr[][] { {Int.ONE}, MVPoly.getIntList(Int.ONE, x.length, i)};
	}
	if(u.isPower())
	{
	    Expr base = u.get(0);
	    Expr exponent = u.get(1);
	    for(int i = 0; i < x.length; i++)
	    {
		if(base.equals(x[i]) && exponent.isInt() && ((Int) exponent).isPositive())
		    return new Expr[][] { {Int.ONE}, MVPoly.getIntList((Int) exponent, x.length, i)};
	    }

	}
	if(u.isProduct())
	{
	    Expr c = u;
	    Int[] m = MVPoly.getIntList(Int.ZERO, x.length);
	    for(int i = 0; i < u.length(); i++)
	    {
		Expr[][] f = coefficient_monomial(u.get(i), x);
		if(f == null)
		    return null;

		if(!Set.equal(f[1], MVPoly.getIntList(Int.ZERO, x.length)))
		{

		    m = Simplification.castToInt(Set.addElementwise(f[1], m));
		}
	    }
	    Expr[] monomial = new Expr[x.length];
	    for(int j = 0; j < monomial.length; j++)
		monomial[j] = new Expr(Operator.POWER, x[j], m[j]);
	    c = u.div(new Expr(Operator.MULTIPLY, monomial));
	    return new Expr[][] { {c}, m};
	}

	if(u.isFreeOf(x))
	    return new Expr[][] { {u}, MVPoly.getIntList(Int.ZERO, x.length)};
	return null;
    }

    public static Expr coefficient_poly(Expr u, Expr x, Int j)
    {
	if(!u.isSum())
	{
	    Expr[] f = coefficient_monomial(u, x);
	    if(f == null)
		return null;
	    if(f[1].equals(j))
		return f[0];
	    return Int.ZERO;
	}
	else
	{
	    Expr c = Int.ZERO;
	    for(int i = 0; i < u.length(); i++)
	    {
		Expr[] f = coefficient_monomial(u.get(i), x);
		if(f == null)
		    return null;
		if(f[1].equals(j))
		    c = c.add(f[0]);
	    }
	    return c;
	}
    }

    public static Expr coefficient_poly_gie(Expr u, Expr x, Int j)
    {
	if(!u.isSum())
	{
	    Expr[] f = coefficient_monomial_gie(u, x);
	    if(f == null)
		return null;
	    if(f[1].equals(j))
		return f[0];
	    return Int.ZERO;
	}
	else
	{
	    Expr c = Int.ZERO;
	    for(int i = 0; i < u.length(); i++)
	    {
		Expr[] f = coefficient_monomial_gie(u.get(i), x);
		if(f == null)
		    return null;
		if(f[1].equals(j))
		    c = c.add(f[0]);
	    }
	    return c;
	}
    }

    public static Expr coefficient_poly_Q(Expr u, Expr x, Int j)
    {
	if(!u.isSum())
	{
	    Expr[] f = Simplification.constant_term(u, x);
	    if(f[1].equals(x.pow(j)))
		return f[0];
	    return Int.ZERO;
	}
	else
	{
	    // Binary search
	    int l = 0;
	    int r = u.length() - 1;
	    Expr x_j = x.pow(j);
	    while(l != r)
	    {
		int m = (int) Math.round((l + r) / 2.0);
		Expr n = u.get(m).div(x_j);
		if(n.isInt())
		    return n;
		if(Expr.compare(u.get(m), x_j) < 0)
		    r = m;
		else
		    l = m;
	    }
	    Expr n = u.get(r).div(x_j);
	    if(n.isInt())
		return n;
	    return Int.ZERO;
	}
    }

    public static Expr coefficient_poly(Expr u, Expr[] x, Int[] j)
    {
	if(x.length == 1)
	    return coefficient_poly(u, x[0], j[0]);
	Expr y = x[0];
	Int n = j[0];
	x = Set.rest(x);
	j = Simplification.castToInt(Set.rest(j));
	Expr c = coefficient_poly(u, y, n);
	if(c == null)
	    return null;
	return coefficient_poly(c, x, j);
    }

    public static Int degree(Expr t, Expr v)
    {
	if(t.equals(Int.ZERO))
	    return Int.NONE;

	if(is_monomial(t, new Expr[] {v}))
	{
	    return (Int) coefficient_monomial(t, v)[1];
	}
	if(is_poly(t, new Expr[] {v}))
	{
	    Int u = Int.NONE;
	    for(int i = 0; i < t.length(); i++)
	    {
		Int d = (Int) coefficient_monomial(t.get(i), v)[1];
		u = d.compareTo(u) > 0 ? d : u;
	    }
	    return u;
	}
	return null;
    }

    public static Int min_degree(Expr t, Expr v)
    {
	if(t.equals(Int.ZERO))
	    return Int.NONE;

	if(is_monomial(t, new Expr[] {v}))
	{
	    return (Int) coefficient_monomial(t, v)[1];
	}
	if(is_poly(t, new Expr[] {v}))
	{
	    Int u = (Int) coefficient_monomial(t.get(0), v)[1];
	    for(int i = 1; i < t.length(); i++)
	    {
		Int d = (Int) coefficient_monomial(t.get(i), v)[1];
		u = d.compareTo(u) < 0 ? d : u;
	    }
	    return u;
	}
	return null;
    }

    public static Int degree_gie(Expr t, Expr v)
    {
	if(t.equals(Int.ZERO))
	    return Int.ZERO;

	if(is_monomial_gie(t, new Expr[] {v}))
	{
	    return (Int) coefficient_monomial_gie(t, v)[1];
	}
	if(is_poly_gie(t, new Expr[] {v}))
	{
	    Int u = (Int) coefficient_monomial_gie(t.get(0), v)[1];
	    for(int i = 1; i < t.length(); i++)
	    {
		Int d = (Int) coefficient_monomial_gie(t.get(i), v)[1];
		u = d.compareTo(u) > 0 ? d : u;
	    }
	    return u;
	}
	return null;
    }

    public static Int min_degree_gie(Expr t, Expr v)
    {
	if(t.equals(Int.ZERO))
	    return Int.ZERO;

	if(is_monomial_gie(t, new Expr[] {v}))
	{
	    return (Int) coefficient_monomial_gie(t, v)[1];
	}
	if(is_poly_gie(t, new Expr[] {v}))
	{
	    Int u = (Int) coefficient_monomial_gie(t.get(0), v)[1];
	    for(int i = 1; i < t.length(); i++)
	    {
		Int d = (Int) coefficient_monomial_gie(t.get(i), v)[1];
		u = d.compareTo(u) < 0 ? d : u;
	    }
	    return u;
	}
	return null;
    }

    public static Int degree_Q(Expr t, Expr v)
    {
	if(t.equals(Int.ZERO))
	    return Int.NONE;
	if(t.isSum())
	{
	    return degree_Q(t.get(t.length() - 1), v);
	}
	else
	{
	    Expr[] f = Simplification.constant_term(t, v);
	    if(f[1].isFreeOf(v))
		return Int.ZERO;
	    else
		return (Int) Simplification.base_exp(f[1])[1];
	}
    }

    private static Expr leading_coef(Expr u, Expr x)
    {
	if(u.equals(Int.ZERO))
	    return Int.ZERO;
	return coefficient_poly(u, x, degree(u, x));
    }

    public static Expr leading_coef_Q(Expr u, Expr x)
    {
	if(u.equals(Int.ZERO))
	    return Int.ZERO;
	return coefficient_poly_Q(u, x, degree_Q(u, x));
    }

    public static Expr leading_coef(Expr u, Expr... x)
    {
	if(x.length == 0)
	    return u;
	if(x.length == 1)
	    return leading_coef(u, x[0]);
	Expr y = x[0];
	Expr[] r = Set.rest(x);
	return leading_coef(leading_coef(u, y), r);
    }

    public static Expr[] coef_var_monomial(Expr u, Expr... x)
    {
	if(Set.member(x, u))
	    return new Expr[] {Int.ONE, u};
	if(u.isFreeOf(x))
	    return new Expr[] {u, Int.ONE};
	if(u.isProduct())
	{
	    Expr v = u.get(0);
	    Expr w = u.div(v);
	    Expr[] K = coef_var_monomial(v, x);
	    Expr[] L = coef_var_monomial(w, x);
	    return new Expr[] {K[0].mul(L[0]), L[1].mul(K[1])};
	}
	if(u.isPower())
	{
	    Expr b = u.get(0);
	    Expr e = u.get(1);
	    if(Set.member(x, b) && e.isInt())
		return new Expr[] {Int.ONE, u};
	}
	return null;
    }

    public static Int poly_height(Expr u, Expr... x)
    {
	if(u.isSum())
	{
	    Int max = Int.ZERO;
	    for(int i = 0; i < u.length(); i++)
	    {
		Int c = (Int) coefficient_monomial(u.get(i), x)[0][0];
		c = c.abs();
		max = max.compareTo(c) >= 0 ? max : c;
	    }
	    return max;
	}
	else
	{
	    Int c = (Int) coefficient_monomial(u, x)[0][0];
	    return c.abs();
	}
    }

    public static Int coefficient_lcm(Expr u, Expr[] x)
    {
	if(x.length == 0)
	{
	    Numerical n = (Numerical) u;
	    if(n.isRational())
		return ((Rational) u).getDenominator();
	    else
		return Int.ONE;
	}
	else
	{
	    Expr y = x[0];
	    Expr[] R = Set.rest(x);
	    if(u.isSum())
	    {
		Int lcm = Int.ONE;
		for(int i = 0; i < u.length(); i++)
		{
		    Expr c = coefficient_monomial(u.get(i), y)[0];
		    Int k = coefficient_lcm(c, R);
		    lcm = Int.lcm(lcm, k);
		}
		return lcm;
	    }
	    else
	    {
		Expr c = coefficient_monomial(u, y)[0];
		Int k = coefficient_lcm(c, R);
		return k;
	    }
	}
    }

    public static Int plus_norm(Expr u, Expr[] vars)
    {
	if(vars.length == 0)
	{
	    return ((Int) u).abs();
	}
	else
	{
	    Expr x = vars[vars.length - 1];
	    Expr[] R = new Expr[vars.length - 1];
	    for(int i = 0; i < R.length; i++)
		R[i] = vars[i];
	    Int max = Int.ZERO;
	    Int n = degree(u, x);
	    for(Int i = Int.ZERO; i.compareTo(n) <= 0; i = i.add(Int.ONE))
	    {
		max = max.add(plus_norm(coefficient_poly(u, x, i), R));
	    }
	    return max;
	}
    }

    public static Expr horner_evaluate(Expr u, Expr x, Expr a)
    {
	if(u.isFreeOf(x))
	    return u;
	Expr c = coefficient_poly(u, x, Int.ZERO);
	Expr v = Algebra.expand(u.sub(c).div(x));
	return Algebra.expand(horner_evaluate(v, x, a).mul(a).add(c));
    }

    public static Expr[] variables(Expr u)
    {
	if(u.isNumerical())
	    return new Expr[] {};
	if(u.isPower())
	{
	    Expr b = u.get(0);
	    Expr e = u.get(1);
	    if(e.isInt() && Simplification.is_positive(e))
		return new Expr[] {b};
	}
	if(u.isProduct() || u.isSum())
	{
	    Vector<Expr[]> vars = new Vector<Expr[]>();
	    for(int i = 0; i < u.length(); i++)
		vars.add(variables(u.get(i)));
	    return Set.union(vars.toArray(new Expr[vars.size()][]));
	}
	return new Expr[] {u};
    }

    public static Expr[] variables_fractional_exponent(Expr u)
    {
	if(u.isNumerical())
	    return new Expr[] {};
	if(u.isPower())
	{
	    Expr b = u.get(0);
	    Expr e = u.get(1);
	    if(e.isNumerical())
		return new Expr[] {b};
	}
	if(u.isProduct() || u.isSum())
	{
	    Vector<Expr[]> vars = new Vector<Expr[]>();
	    for(int i = 0; i < u.length(); i++)
		vars.add(variables_fractional_exponent(u.get(i)));
	    return Set.union(vars.toArray(new Expr[vars.size()][]));
	}
	return new Expr[] {u};
    }

    public static boolean are_poly(Expr[] a, Expr[] b)
    {
	for(int i = 0; i < a.length; i++)
	    if(!is_poly(a[i], b))
		return false;
	return true;
    }

    public static boolean is_rational_f(Expr a, Expr... x)
    {
	Expr[] nd = Algebra.NumeratorDenominator(a);
	return is_poly(nd[0], x) && is_poly(nd[1], x);
    }
}
