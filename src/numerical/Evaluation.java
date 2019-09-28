package numerical;

import Expression.Expr;
import Expression.Operator;
import Symbolic.*;
import Simplification.*;

public class Evaluation 
{
	public static Expr evaluate(Expr u, int p)
	{
		int d = Decimal.DEFAULT_PRECISION;
		Decimal.DEFAULT_PRECISION = p;
		Expr s = eval(u, p);
		Decimal.DEFAULT_PRECISION = d;
		return s;
	}

	public static Expr eval(Expr u, int p)
	{
		if(u.isSymbolic())
		{
			if(u.isRational())
				return ((Rational)u).toDecimal(); 
		    return u;
		}
		Expr[] v = new Expr[u.length()];
		for(int i = 0;i<v.length;i++)
			v[i] = eval(u.get(i), p);
		if(u.getOperator().equals(Operator.EXP))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.exp(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.LOG))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.log(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.POWER))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			Decimal[] gr2 = gaussian_rational(v[1], p);
			if(gr != null && gr2 != null)
			{
				Decimal[] c = NumericalApfloat.pow(gr, gr2, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.SIN))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.sin(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.COS))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.cos(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.TAN))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.tan(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.ARCSIN))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.arcsin(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.ARCCOS))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.arccos(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.ARCTAN))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.arctan(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.SINH))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.sinh(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.COSH))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.cosh(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		if(u.getOperator().equals(Operator.ABSOLUTE_VALUE))
		{
			Decimal[] gr = gaussian_rational(v[0], p);
			if(gr != null)
			{
				Decimal[] c = NumericalApfloat.abs(gr, p);
				return c[0].add(c[1].mul(Constant.I));
			}
		}
		return Simplification.simplify_recursive(new Expr(u.getOperator(), v));
	}
	
	public static Decimal[] gaussian_rational(Expr v, int p)
	{
		if(v.equals(Int.ZERO))
			return new Decimal[]{Int.ZERO.toDecimal(), Int.ZERO.toDecimal()};
		if(v.isNumerical())
			return new Decimal[]{((Numerical)v).toDecimal(), Int.ZERO.toDecimal()};
		if(v.equals(Constant.I))
			return new Decimal[]{Int.ZERO.toDecimal(), Int.ONE.toDecimal()};
		if(v.isProduct() && v.length() == 2)
		{
			Expr A = v.get(0);
			Expr B = v.get(1);
			if(A.isNumerical() && B.equals(Constant.I))
				return new Decimal[]{Int.ZERO.toDecimal(), ((Numerical)A).toDecimal()};
		}
		if(v.isSum() && v.length() == 2)
		{
			Expr A = v.get(0);
			Expr B = v.get(1);
			if(A.isNumerical() && B.equals(Constant.I))
				return new Decimal[]{((Numerical)A).toDecimal(), Int.ONE.toDecimal()};
			if(A.isNumerical() && B.isProduct() && B.length() == 2)
			{
				Expr B_1 = B.get(0);
				Expr B_2 = B.get(1);
				if(B_1.isNumerical() && B_2.equals(Constant.I))
					return new Decimal[]{((Numerical)A).toDecimal(), ((Numerical)B_1).toDecimal()};
			}
		}
		return null;
	}
}
