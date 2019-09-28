package Expression;

import java.io.Serializable;

import algebra.Algebra;
import algebra.MatchForm;
import polynomial.Poly;
import Simplification.Simplification;
import Symbolic.*;

public class Expr implements Serializable
{

    Expr[] operands;
    Operator op;

    public static Expr EMPTY_SET = new Expr(Operator.SET, new Expr(Operator.LIST));
    public static Expr FULL_SET = new Expr(Operator.SET, new Var("&0"), Constant.TRUE);

    public Expr(Operator op, Expr... ops)
    {
	this.op = op;
	operands = ops;
    }

    public Operator getOperator()
    {
	if(op == null)
	    return Operator.NULL;
	return op;
    }

    public Expr[] getOperands()
    {
	Expr[] p = new Expr[operands.length];
	for(int i = 0; i < p.length; i++)
	    p[i] = operands[i];
	return p;
    }

    public int length()
    {
	return operands.length;
    }

    public Expr get(int k)
    {
	return operands[k];
    }

    public Expr substitute(Expr var, Expr v)
    {
	return this.substitute(new Expr[] {var}, new Expr[] {v});
    }

    public Expr substitute(Expr[] vars, Expr[] vs)
    {
	for(int i = 0; i < vars.length; i++)
	{
	    if(this.equals(vars[i]))
		return vs[i];
	}

	if(this instanceof Symbolic)
	    return this;
	if(this.getOperator().equals(Operator.FDERIV))
	    return this;
	Expr[] e = new Expr[this.length()];
	for(int i = 0; i < e.length; i++)
	{
	    for(int j = 0; j < vars.length; j++)
	    {
		if(this.get(i).equals(vars[j]) && vs[j].getOperator().equals(Operator.ARGS))
		{
		    Expr[] a = vs[j].getOperands();
		    Expr[] args = new Expr[e.length + a.length - 1];
		    for(int k = 0; k < i; k++)
			args[k] = this.get(k);

		    for(int k = i; k < a.length + i; k++)
			args[k] = a[k - i];
		    for(int k = i + a.length; k < args.length; k++)
			args[k] = this.get(k - a.length + 1);
		    return new Expr(this.getOperator(), args).substitute(vars, vs);
		}
	    }
	    e[i] = this.get(i).substitute(vars, vs);
	}
	return new Expr(this.getOperator(), e);
    }

    public Expr substitute_root(Expr[] vars, Expr[] vs)
    {

	for(int i = 0; i < vars.length; i++)
	{
	    if(this.equals(vars[i]))
		return vs[i];
	}

	if(this.isPower() && this.get(1).isRational())
	{
	    Expr b = this.get(0);
	    Rational e = (Rational) this.get(1);
	    for(int i = 0; i < vars.length; i++)
	    {
		Expr[] cd = Simplification.base_exp(vars[i]);
		if(cd[1].isRational() && cd[0].equals(b))
		{
		    Rational d = (Rational) cd[1];
		    if(e.getNumerator().mod(d.getNumerator()).equals(Int.ZERO)
			    && e.getDenominator().equals(d.getDenominator()))
			return vs[i].pow(e.getNumerator().divide(d.getNumerator()));
		}
	    }
	}

	if(this instanceof Symbolic)
	    return this;

	Expr[] e = new Expr[this.length()];
	for(int i = 0; i < e.length; i++)
	{
	    e[i] = this.get(i).substitute_root(vars, vs);
	}
	return new Expr(this.getOperator(), e);
    }

    public boolean isFreeOf(Expr e)
    {
	if(e.equals(this))
	    return false;
	if(this instanceof DExtension)
	    return ((DExtension) this).getArg().isFreeOf(e);
	if(this instanceof Symbolic)
	    return true;
	for(int i = 0; i < this.length(); i++)
	{
	    if(!this.get(i).isFreeOf(e))
		return false;
	}
	return true;
    }

    public boolean isFreeOf(Expr[] e)
    {
	for(int i = 0; i < e.length; i++)
	{
	    if(e[i].equals(this))
		return false;
	}
	if(this instanceof DExtension)
	    return ((DExtension) this).getArg().isFreeOf(e);
	if(this instanceof Symbolic)
	    return true;
	for(int i = 0; i < this.length(); i++)
	{
	    if(!this.get(i).isFreeOf(e))
		return false;

	}
	return true;
    }

    public boolean contains(Expr[] e)
    {
	for(int i = 0; i < e.length; i++)
	{
	    if(this.isFreeOf(new Expr[] {e[i]}))
		return false;
	}
	return true;
    }

    public boolean equals(Expr b)
    {
	if(this instanceof Symbolic && b instanceof Symbolic)
	{
	    return ((Symbolic) this).equals((Symbolic) b);
	}
	if(this instanceof Symbolic && !(b instanceof Symbolic))
	    return false;
	if(!(this instanceof Symbolic) && b instanceof Symbolic)
	    return false;
	if(!this.getOperator().equals(b.getOperator()))
	    return false;
	if(this.length() != b.length())
	    return false;
	for(int i = 0; i < this.length(); i++)
	{
	    if(!this.get(i).equals(b.get(i)))
		return false;
	}
	return true;
    }

    public String toString()
    {
	return toString2();
    }

    public String toStringUniCode()
    {
	String s = this.toString();
	s = s.replaceAll("\\*", "\u2219");
	s = s.replaceAll("%pi", "\u03c0");
	return s;
    }

    public String toStringF()
    {
	if(this instanceof Symbolic)
	{
	    return ((Symbolic) this).toString();
	}

	String s = "";
	for(int i = 0; i < this.length(); i++)
	{
	    if(i != this.length() - 1)
		s += this.get(i).toStringF() + ", ";
	    else
		s += this.get(i).toStringF();
	}
	return this.getOperator().getName() + "(" + s + ")";
    }

    public boolean isNumerical()
    {
	return this instanceof Numerical;
    }

    public boolean isSymbolic()
    {
	return this instanceof Symbolic;
    }

    public boolean isVar()
    {
	return this instanceof Var;
    }

    public boolean isInt()
    {
	return this instanceof Int;
    }

    public boolean isRational()
    {
	return this instanceof Rational;
    }

    public boolean isDecimal()
    {
	return this instanceof Decimal;
    }

    public boolean isLogicalConstant()
    {
	return this.equals(Constant.FALSE) || this.equals(Constant.TRUE);
    }

    public boolean isFinite()
    {
	return !(this.equals(Constant.POS_INF) || this.equals(Constant.NEG_INF));
    }

    public boolean isSum()
    {
	return this.getOperator().equals(Operator.ADD);
    }

    public boolean isProduct()
    {
	return this.getOperator().equals(Operator.MULTIPLY);
    }

    public boolean isPower()
    {
	return this.getOperator().equals(Operator.POWER);
    }

    public boolean isHold()
    {
	return this.getOperator().equals(Operator.HOLD);
    }

    public static int compare(Expr u, Expr v)
    {
	if(u.isNumerical() && v.isNumerical())
	    return -((Numerical) u).compareTo((Numerical) v);
	if(u instanceof ModIntSym && v instanceof ModIntSym)
	{
	    int c = -((ModIntSym) u).toInt().compareTo(((ModIntSym) v).toInt());
	    if(c != 0)
		return c;
	    return -((ModIntSym) u).getModulus().compareTo(((ModIntSym) v).getModulus());
	}
	if(u instanceof ModIntNon && v instanceof ModIntNon)
	{
	    int c = -((ModIntNon) u).toInt().compareTo(((ModIntNon) v).toInt());
	    if(c != 0)
		return c;
	    return -((ModIntNon) u).getModulus().compareTo(((ModIntNon) v).getModulus());
	}
	if(u.isVar() && v.isVar())
	    return -((Var) u).getName().compareTo(((Var) v).getName());
	if(u instanceof Str && v instanceof Str)
	    return -((Str) u).toString().compareTo(((Str) v).toString());
	if((u.isSum() && v.isSum()) || (u.isProduct() && v.isProduct()))
	{
	    int m = u.length();
	    int n = v.length();

	    if(!u.getOperands()[m - 1].equals(v.getOperands()[n - 1]))
		return compare(u.getOperands()[m - 1], v.getOperands()[n - 1]);
	    int min = Math.min(m, n);
	    for(int i = 1; i < min; i++)
	    {
		if(!u.getOperands()[m - 1 - i].equals(v.getOperands()[n - 1 - i]))
		    return compare(u.getOperands()[m - 1 - i], v.getOperands()[n - 1 - i]);
	    }
	    if(m < n)
		return 1;
	    else
		return -1;
	}
	if(u.isPower() && v.isPower())
	{
	    Expr[] a = u.getOperands();
	    Expr[] b = v.getOperands();
	    if(!a[0].equals(b[0]))
		return compare(a[0], b[0]);
	    else
		return compare(a[1], b[1]);
	}

	if(u.isFunctionForm() && v.isFunctionForm())
	{
	    if(!u.getOperator().equals(v.getOperator()))
		return -u.getOperator().getName().compareTo(v.getOperator().getName());// u.getOperator().getPriority()
										       // >=
										       // v.getOperator().getPriority();
	    else
	    {
		int m = u.length();
		int n = v.length();

		if(n > 0 && m > 0 && !u.getOperands()[m - 1].equals(v.getOperands()[n - 1]))
		    return compare(u.getOperands()[m - 1], v.getOperands()[n - 1]);
		int min = Math.min(m, n);
		for(int i = 1; i < min; i++)
		{
		    if(!u.getOperands()[m - 1 - i].equals(v.getOperands()[n - 1 - i]))
			return compare(u.getOperands()[m - 1 - i], v.getOperands()[n - 1 - i]);
		}
		if(m < n)
		    return 1;
		else
		    return -1;
	    }
	}
	if(u.isNumerical())
	    return 1;
	if(v.isNumerical())
	    return -1;
	if(u instanceof ModIntSym)
	    return 1;
	if(v instanceof ModIntSym)
	    return -1;
	if(u instanceof ModIntNon)
	    return 1;
	if(v instanceof ModIntNon)
	    return -1;
	if(u.isProduct() && (v.isSum() || v.isVar() || v.isPower() || v.isFunctionForm()))
	    return compare(u, new Expr(Operator.MULTIPLY, v));
	if(u.isPower() && (v.isSum() || v.isVar() || v.isFunctionForm()))
	    return compare(u, new Expr(Operator.POWER, v, Int.ONE));
	if(u.isSum() && (v.isFunctionForm() || v.isVar()))
	    return compare(u, new Expr(Operator.ADD, v));
	if(u.isFunctionForm() && v.isVar())
	{
	    String v_name = ((Var) v).getName();
	    String u_name = u.getOperator().getName();
	    if(u_name.equals(v_name))
		return -1;
	    else
		return -u_name.compareTo(v_name);
	}
	return -compare(v, u);
    }

    private boolean isFunctionForm()
    {
	return this.getOperator().type.equals("function");
    }

    public Expr add(Expr b)
    {
	return Simplification.simplify_recursive(new Expr(Operator.ADD, this, b));
    }

    public Expr sub(Expr b)
    {
	return Simplification.simplify_recursive(new Expr(Operator.ADD, this, new Expr(
		Operator.MULTIPLY, Int.NONE, b)));
    }

    public Expr div(Expr b)
    {
	return Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, this, new Expr(
		Operator.POWER, b, Int.NONE)));
    }

    public Expr mul(Expr b)
    {
	return Simplification.simplify_recursive(new Expr(Operator.MULTIPLY, this, b));
    }

    public Expr pow(Expr b)
    {
	return Simplification.simplify_recursive(new Expr(Operator.POWER, this, b));
    }

    public Expr sqrt()
    {
	return this.pow(Rational.HALF);
    }

    public Expr artanh()
    {
	return Rational.HALF.mul(new Expr(Operator.LOG, this.add(Int.ONE)).sub(new Expr(
		Operator.LOG, this.sub(Int.ONE))));
    }

    public Expr exp()
    {
	return Simplification.simplify_recursive(new Expr(Operator.EXP, this));
    }

    public Expr log()
    {
	return Simplification.simplify_recursive(new Expr(Operator.LOG, this));
    }

    public Expr sin()
    {
	return Simplification.simplify_recursive(new Expr(Operator.SIN, this));
    }

    public Expr cos()
    {
	return Simplification.simplify_recursive(new Expr(Operator.COS, this));
    }

    public Expr abs()
    {
	return Simplification.simplify_recursive(new Expr(Operator.ABSOLUTE_VALUE, this));
    }

    public String toString2()
    {
	if(this instanceof Symbolic)
	{
	    if(this.isInt())
	    {
		Int a = (Int) this;
		if(a.isPositive() || a.isZero())
		    return a.toString();
		else
		    return a.toString();
	    }
	    if(this.isDecimal())
	    {
		return ((Decimal) this).toString();
	    }
	    if(this.isRational())
	    {

		Rational a = (Rational) this;

		if(a.compareTo(Int.ZERO) == -1)
		    return a.getNumerator().toString() + "/" + a.getDenominator().toString();
		else
		    return a.getNumerator().toString() + "/" + a.getDenominator().toString();
	    }
	    return ((Symbolic) this).toString();
	}

	Expr[] nd = Algebra.NumeratorDenominator(this, true);
	if(!nd[1].isInt())
	{
	    String nom;
	    String denom;
	    if(nd[0].isSum() || nd[0].isRational())
		nom = "(" + nd[0].toString2() + ")";
	    else
		nom = nd[0].toString2();

	    if(nd[1].isSum() || nd[1].isProduct() || nd[1].isRational())
		denom = "(" + nd[1].toString2() + ")";
	    else
		denom = nd[1].toString2();
	    return nom + "/" + denom;
	}
	if(this.isSum())
	{
	    String sum = "";
	    for(int i = 0; i < this.length(); i++)
	    {
		Expr c = this.get(i);
		String sign = "+";

		if(((Numerical) Simplification.constant_term(c)[0]).compareTo(Int.ZERO) < 0)
		{
		    c = c.mul(Int.NONE);
		    sign = "-";
		}
		String c_str = c.toString2();
		if(c.isSum() || c.isHold())
		    c_str = "(" + c_str + ")";
		if(i == 0)
		{
		    if(sign.equals("-"))
			sum += "-" + c_str;
		    else
			sum += c_str;
		}
		else
		    sum += sign + c_str;
	    }
	    return sum;
	}
	if(this.isProduct())
	{
	    Expr r = this;
	    String product = "";
	    if(((Numerical) Simplification.constant_term(r)[0]).compareTo(Int.ZERO) < 0)
	    {
		r = r.mul(Int.NONE);
		product = "-";
	    }
	    if(!r.isProduct())
	    {
		if(r.isSum())
		    return product + "(" + r.toString2() + ")";
		return product + r.toString2();
	    }
	    for(int i = 0; i < r.getOperands().length; i++)
	    {
		if(r.getOperands()[i].isSum())
		{
		    if(i == 0)
			product += "(" + r.getOperands()[i].toString2() + ")";
		    else
			product += "*" + "(" + r.getOperands()[i].toString2() + ")";
		}
		else
		{
		    if(i == 0)
			product += r.getOperands()[i].toString2();
		    else
			product += "*" + r.getOperands()[i].toString2();
		}
	    }
	    return product;
	}
	if(this.isPower())
	{
	    Expr[] be = Simplification.base_exp(this);
	    if(be[1].equals(new Rational(Int.ONE, Int.TWO)))
		return "sqrt(" + be[0].toString2() + ")";
	    String b;
	    String e;
	    if(be[0].isSum() || be[0].isProduct() || be[0].isPower() ||
		    (be[0].isInt() && ((Int) be[0]).isNegative()) || be[0].isRational())
		b = "(" + be[0].toString2() + ")";
	    else
		b = be[0].toString2();
	    if(be[1].isSum() || be[1].isProduct() || be[1].isPower() || be[1].isRational())
		e = "(" + be[1].toString2() + ")";
	    else
		e = be[1].toString2();
	    return b + "^" + e;
	}
	if(this.getOperator().equals(Operator.LIST))
	{
	    if(this.getOperands().length == 0)
		return "{}";

	    String tmp = this.getOperands()[0].toString2();
	    for(int u = 1; u < this.getOperands().length; u++)
		tmp = tmp + "," + this.getOperands()[u].toString2();
	    return "{" + tmp + "}";
	}
	if(this.getOperator().equals(Operator.SET))
	{
	    if(this.length() == 1)
		return "s" + this.get(0).toString2();
	    return "s{" + this.get(0).toString2() + "|" + this.get(1).toString2() + "}";

	}
	if(this.getOperator().equals(Operator.MATRIX))
	{
	    return "m" + this.get(0).toString2();
	}
	if(this.getOperator().equals(Operator.EQUAL))
	{
	    return this.getOperands()[0].toString2() + "=" + this.getOperands()[1].toString2();
	}
	if(this.getOperator().equals(Operator.BIGGER))
	{
	    return this.getOperands()[0].toString2() + " > " + this.getOperands()[1].toString2();
	}
	if(this.getOperator().equals(Operator.SMALLER))
	{
	    return this.getOperands()[0].toString2() + " < " + this.getOperands()[1].toString2();
	}
	if(this.getOperator().equals(Operator.BIGGER_EQUAL))
	{
	    return this.getOperands()[0].toString2() + " >= " + this.getOperands()[1].toString2();
	}
	if(this.getOperator().equals(Operator.SMALLER_EQUAL))
	{
	    return this.getOperands()[0].toString2() + " =< " + this.getOperands()[1].toString2();
	}
	if(this.getOperator().equals(Operator.OR))
	{
	    String s = this.get(0).toString2();
	    for(int i = 1; i < this.length(); i++)
		s += " or " + this.get(i).toString2();
	    return s;
	}
	if(this.getOperator().equals(Operator.AND))
	{
	    String s = this.get(0).toString2();
	    for(int i = 1; i < this.length(); i++)
	    {
		if(this.get(i).getOperator().equals(Operator.OR))
		    s += " and (" + this.get(i).toString2() + ")";
		else
		    s += " and " + this.get(i).toString2();
	    }
	    return s;
	}
	if(this.getOperator().equals(Operator.HOLD))
	    return this.get(0).toString2();
	if(this.getOperator().equals(Operator.FACTORIAL))
	{
	    if(this.get(0).isSymbolic())
		return this.get(0).toString2() + "!";
	    return "(" + this.get(0).toString2() + ")!";
	}
	if(this.getOperator().equals(Operator.FDERIV) && !this.get(2).isList())
	{
	    Operator f = (Operator) this.get(0);
	    Expr n = this.get(1);
	    Expr x = this.get(2);
	    if(n.isInt())
	    {
		int N = ((Int) n).toInt();
		if(N <= 3 && N > 0)
		{
		    String p = "";
		    for(int i = 1; i <= N; i++)
			p += "'";
		    return f.getName() + p + "(" + x.toString2() + ")";
		}
	    }
	}
	String tmp = this.get(0).toString2();
	for(int u = 1; u < this.getOperands().length; u++)
	    tmp = tmp + "," + this.getOperands()[u].toString2();
	return this.getOperator().getName() + "(" + tmp + ")";

    }

    public boolean isList()
    {
	return this.getOperator().equals(Operator.LIST);
    }

    public Expr[] rest()
    {
	Expr[] s = new Expr[operands.length - 1];
	for(int i = 0; i < s.length; i++)
	    s[i] = operands[i + 1];
	return s;

    }

    public boolean isSet()
    {
	return this.getOperator().equals(Operator.SET);
    }

    public boolean isSqrt()
    {
	if(this.isPower() && this.get(1).equals(Rational.HALF))
	    return true;
	return false;
    }

    public static boolean isFreeOf(Expr[] e, Expr... v)
    {
	for(int i = 0; i < e.length; i++)
	    if(!e[i].isFreeOf(v))
		return false;
	return true;
    }

    public static String toString(Expr[] v)
    {
	String s = "[";
	for(int i = 0; i < v.length; i++)
	{
	    if(v[i] == null)
	    {
		if(i != 0)
		    s += ", " + "NULL";
		else
		    s += "NULL";
	    }
	    else if(i != 0)
		s += ", " + v[i].toString2();
	    else
		s += v[i].toString2();
	}
	return s + "]";
    }

    public static String toString(Expr[][] v)
    {
	String s = "[";
	for(int i = 0; i < v.length; i++)
	{
	    if(i != 0)
		s += ", " + toString(v[i]);
	    else
		s += toString(v[i]);
	}
	return s + "]";
    }

    public static String toString(Expr[][][] v)
    {
	String s = "[";
	for(int i = 0; i < v.length; i++)
	{
	    if(i != 0)
		s += ", " + toString(v[i]);
	    else
		s += toString(v[i]);
	}
	return s + "]";
    }

    public boolean isNaturalNumber()
    {
	return this.isInt() && ((Int) this).isPositive();
    }

    public boolean isLinear(Expr x)
    {
	if(MatchForm.linear_form(this, x) != null)
	    return true;
	return false;
    }

    public boolean isMatrix()
    {
	return this.getOperator().equals(Operator.MATRIX);
    }

}
