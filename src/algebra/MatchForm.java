package algebra;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import polynomial.Poly;
import Expression.Expr;
import Expression.Operator;
import Helper.Helper;
import Simplification.Set;
import Symbolic.Int;

public class MatchForm
{

    public static Expr[] linear_form(Expr u, Expr x)
    {
	if(u.equals(x))
	    return new Expr[] {Int.ONE, Int.ZERO};
	if(u.isNumerical())
	    return new Expr[] {Int.ZERO, u};
	if(u.isProduct())
	{
	    if(u.isFreeOf(x))
		return new Expr[] {Int.ZERO, u};
	    Expr v = u.div(x);
	    if(v.isFreeOf(x))
		return new Expr[] {v, Int.ZERO};
	    return null;
	}
	if(u.isSum())
	{
	    Expr[] v = linear_form(u.get(0), x);
	    Expr[] w = linear_form(u.sub(u.get(0)), x);
	    if(w == null || v == null)
		return null;
	    Expr[] r = new Expr[] {v[0].add(w[0]), v[1].add(w[1])};
	    return r;
	}
	if(u.isFreeOf(x))
	    return new Expr[] {Int.ZERO, u};
	return null;
    }

    public static Expr[] quadratic_form(Expr u, Expr x)
    {
	if(u.equals(x))
	    return new Expr[] {Int.ZERO, Int.ONE, Int.ZERO};
	if(u.equals(x.pow(Int.TWO)))
	    return new Expr[] {Int.ONE, Int.ZERO, Int.ZERO};
	if(u.isNumerical())
	    return new Expr[] {Int.ZERO, Int.ZERO, u};
	if(u.isProduct())
	{
	    if(u.isFreeOf(x))
		return new Expr[] {Int.ZERO, Int.ZERO, u};
	    Expr v = u.div(x);
	    if(v.isFreeOf(x))
		return new Expr[] {Int.ZERO, v, Int.ZERO};
	    v = v.div(x);
	    if(v.isFreeOf(x))
		return new Expr[] {v, Int.ZERO, Int.ZERO};
	    return null;
	}
	if(u.isSum())
	{
	    Expr[] v = quadratic_form(u.get(0), x);
	    Expr[] w = quadratic_form(u.sub(u.get(0)), x);
	    if(w == null || v == null)
		return null;
	    Expr[] r = new Expr[] {v[0].add(w[0]), v[1].add(w[1]), v[2].add(w[2])};
	    return r;
	}
	if(u.isFreeOf(x))
	    return new Expr[] {Int.ZERO, Int.ZERO, u};
	return null;
    }

    public static Expr[] exp_sin_product(Expr u, Expr x)
    {
	if(u.isSymbolic())
	    return null;
	if(u.isProduct())
	{
	    Expr a = Int.ZERO, b = Int.ZERO, c = Int.ZERO, d = Int.ZERO;
	    boolean got_sin = false;
	    for(int i = 0; i < u.length(); i++)
	    {
		Expr y = u.get(i);
		if(y.getOperator().equals(Operator.SIN) && !got_sin)
		{
		    Expr[] m = linear_form(y.get(0), x);
		    if(m == null)
			return null;
		    got_sin = true;
		    c = m[0];
		    d = m[1];
		}
		else if(y.getOperator().equals(Operator.EXP))
		{
		    Expr[] m = linear_form(y.get(0), x);
		    if(m == null)
			return null;
		    a = a.add(m[0]);
		    b = b.add(m[1]);
		}
		else
		    return null;
	    }
	    if(got_sin == false)
		return null;
	    if(a.equals(Int.ZERO) && b.equals(Int.ZERO))
		return null;
	    if(c.equals(Int.ZERO) && d.equals(Int.ZERO))
		return null;
	    return new Expr[] {a, b, c, d};
	}
	else
	    return exp_sin_product(new Expr(Operator.MULTIPLY, u), x);
    }

    public static Expr[] exp_cos_product(Expr u, Expr x)
    {
	if(u.isSymbolic())
	    return null;
	if(u.isProduct())
	{
	    Expr a = Int.ZERO, b = Int.ZERO, c = Int.ZERO, d = Int.ZERO;
	    boolean got_cos = false;
	    for(int i = 0; i < u.length(); i++)
	    {
		Expr y = u.get(i);
		if(y.getOperator().equals(Operator.COS) && !got_cos)
		{
		    Expr[] m = linear_form(y.get(0), x);
		    if(m == null)
			return null;
		    got_cos = true;
		    c = m[0];
		    d = m[1];
		}
		else if(y.getOperator().equals(Operator.EXP))
		{
		    Expr[] m = linear_form(y.get(0), x);
		    if(m == null)
			return null;
		    a = a.add(m[0]);
		    b = b.add(m[1]);
		}
		else
		    return null;
	    }
	    if(got_cos == false)
		return null;
	    if(a.equals(Int.ZERO) && b.equals(Int.ZERO))
		return null;
	    if(c.equals(Int.ZERO) && d.equals(Int.ZERO))
		return null;
	    return new Expr[] {a, b, c, d};
	}
	else
	    return exp_cos_product(new Expr(Operator.MULTIPLY, u), x);
    }

    public static Expr[] sin_cos_product(Expr u, Expr x)
    {
	if(u.isSymbolic())
	    return null;
	if(u.isProduct() && u.length() == 2)
	{
	    Expr A = u.get(0);
	    Expr B = u.get(1);
	    if(A.getOperator().equals(Operator.SIN) && B.getOperator().equals(Operator.COS))
	    {
		Expr[] m = linear_form(A.get(0), x);
		Expr[] n = linear_form(B.get(0), x);
		if(n == null || m == null)
		    return null;
		return new Expr[] {m[0], m[1], n[0], n[1]};
	    }
	    if(A.getOperator().equals(Operator.COS) && B.getOperator().equals(Operator.SIN))
	    {
		Expr[] m = linear_form(A.get(0), x);
		Expr[] n = linear_form(B.get(0), x);
		if(n == null || m == null)
		    return null;
		return new Expr[] {n[0], n[1], m[0], m[1]};
	    }
	}
	return null;
    }

    // u = a*log(c*x+d)*b --> {a, b, c, d}
    public static Expr[] linear_log_form(Expr u, Expr x)
    {
	Expr[] ll = get_linear_logs(u, x);
	for(int i = 0; i < ll.length; i++)
	{
	    Expr[] lf = linear_form(ll[i].get(0), x);
	    if(!lf[0].equals(Int.ZERO))
	    {
		Expr[] l = linear_form(u, ll[i]);
		if(l != null)
		{
		    if(l[0].isFreeOf(x) && l[1].isFreeOf(x))
			return new Expr[] {l[0], l[1], lf[0], lf[1]};
		}
	    }
	}
	return null;
    }

    private static Expr[] get_linear_logs(Expr u, Expr x)
    {
	if(u.isSymbolic())
	    return new Expr[] {};
	if(u.getOperator().equals(Operator.LOG))
	{
	    Expr[] linear = linear_form(u.get(0), x);
	    if(linear != null)
		return new Expr[] {u};
	}
	Expr[] ll = new Expr[] {};
	for(int i = 0; i < u.length(); i++)
	    ll = Set.add(ll, get_linear_logs(u.get(i), x));
	return ll;
    }
    
    public static List<Expr> get_rational_independent(List<Expr> u, Expr x)
    {
	if(u.isEmpty())
	    return u;
	List<Expr> list = new LinkedList<>();
	Iterator<Expr> uIt = u.iterator();
	list.add(uIt.next());
	while(uIt.hasNext())
	{
	    Expr t = uIt.next();
	    Expr n = Helper.apply(Helper.sort(t.getOperands(), e -> e.isFreeOf(x)).getSecond(), t.getOperator());
	    boolean wasMatch = false;
	    for(int i = 0;i<list.size();i++)
	    {
		Expr s = list.get(i);
		Expr d = Helper.apply(Helper.sort(s.getOperands(), e -> e.isFreeOf(x)).getSecond(), s.getOperator());
		if(Poly.is_rational_f(Algebra.cancel(n.div(d)), x))
		{
		    wasMatch = true;
		    list.set(i, s.add(t));
		    break;
		}
	    }
	    if(!wasMatch)
		list.add(t);
	}
	return list;
    }
}
