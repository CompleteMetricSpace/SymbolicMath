package Simplification;

import algebra.AlgebraicNumberField;
import algebra.MatchForm;
import algebra.Series;
import Expression.Expr;
import Expression.Operator;
import Expression.Parser;
import Symbolic.Constant;
import Symbolic.Int;
import Symbolic.Numerical;
import Symbolic.Rational;

public class SimplifyFunctions 
{
	
	private static Expr[][] sin_pi_values = 
		{
		    {Int.ZERO, Int.ZERO}, 
		    {Int.ONE, Int.ZERO},
		    {Rational.HALF, Int.ONE},
		    {new Rational("1", "4"), Int.TWO.sqrt().div(Int.TWO)},
		    {new Rational("3", "4"), Int.TWO.sqrt().div(Int.TWO)},
		    {new Rational("1", "6"), Rational.HALF},
		    {new Rational("5", "6"), Rational.HALF},
		    {new Rational("1", "3"), Int.THREE.sqrt().div(Int.TWO)},
		    {new Rational("2", "3"), Int.THREE.sqrt().div(Int.TWO)},
		};
	
	private static Expr[][] arcsin_values = 
		{
		    {Int.ZERO, Int.ZERO}, 
		    {Int.ONE, Constant.PI.div(Int.TWO)},
		    {Int.TWO.sqrt().div(Int.TWO), Constant.PI.div(Int.FOUR)},
		    {Int.THREE.sqrt().div(Int.TWO), Constant.PI.div(Int.THREE)},
		    {Rational.HALF, Constant.PI.div(Int.SIX)},
		};
	
	private static Expr[][] arccos_values = 
		{
		    {Int.ZERO, Constant.PI.div(Int.TWO)}, 
		    {Int.ONE, Int.ZERO},
		    {Int.TWO.sqrt().div(Int.TWO), Constant.PI.div(Int.FOUR)},
		    {Int.THREE.sqrt().div(Int.TWO), Constant.PI.div(Int.SIX)},
		    {Rational.HALF, Constant.PI.div(Int.THREE)},
		};

	private static Expr[][] arctan_values = 
		{
		    {Int.ZERO, Int.ZERO}, 
		    {Int.ONE, Constant.PI.div(Int.FOUR)},
		    {Int.THREE.sqrt().div(Int.THREE), Constant.PI.div(Int.SIX)},
		    {Int.THREE.sqrt(), Constant.PI.div(Int.THREE)},
		    {Int.TWO.sqrt().sub(Int.ONE), Constant.PI.div(Int.EIGHT)},
		};
	
	
	public static Expr simplify_exp(Expr a)
	{
		if(a.equals(Int.ZERO))
			return Int.ONE;
		if(a.getOperator().equals(Operator.LOG))
			return a.get(0);
		if(a.getOperator().equals(Operator.PSERIES))
		{
			Series s = new Series(a.get(0).getOperands()).exp();
			return new Expr(Operator.PSERIES, new Expr(Operator.LIST, s.getCoefs()), a.get(1));
		}
		Expr s = a.isSum()?a:new Expr(Operator.ADD, a);
		Expr r = Int.ZERO;
		Expr v = Int.ONE;
		for(int i = 0;i<s.length();i++)
		{
			Expr[] ct = Simplification.constant_term(s.get(i));
			if(ct[1].getOperator().equals(Operator.LOG))
				v = v.mul(ct[1].get(0).pow(ct[0]));
			else
				r = r.add(s.get(i));
		}
		if(!v.equals(Int.ONE))
			return v.mul(new Expr(Operator.EXP, r));
		return new Expr(Operator.EXP, a);
	}
	
	public static Expr simplify_log(Expr a)
	{
		if(a.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(a.equals(Int.ONE))
			return Int.ZERO;
		if(a.isNumerical())
		{
			Numerical n = (Numerical)a;
			if(n.compareTo(Int.ONE) < 0 && n.compareTo(Int.ZERO) > 0)
				return Int.NONE.mul(new Expr(Operator.LOG, Int.ONE.div(n)));
		}
		if(a.getOperator().equals(Operator.PSERIES))
		{
			Series s = new Series(a.get(0).getOperands());
			s = s.set(s.getCoef(0).sub(Int.ONE), 0);
			s = Series.log(s.getLength()).compose(s);
			return new Expr(Operator.PSERIES, new Expr(Operator.LIST, s.getCoefs()), a.get(1));
		}
		if(a.getOperator().equals(Operator.EXP))
			return a.get(0);
		Expr s = a.isProduct()?a:new Expr(Operator.MULTIPLY, a);
		Expr r = Int.ONE;
		Expr v = Int.ZERO;
		for(int i = 0;i<s.length();i++)
		{
			Expr[] ct = Simplification.base_exp(s.get(i));
			if(ct[0].getOperator().equals(Operator.EXP))
				v = v.add(ct[0].get(0).mul(ct[1]));
			else
				r = r.mul(s.get(i));
		}
		if(!v.equals(Int.ZERO))
			return v.add(new Expr(Operator.LOG, r));
		return new Expr(Operator.LOG, a);
	}
	
	public static Expr simplify_sin(Expr a)
	{
		if(is_negative(a))
			return Int.NONE.mul(simplify_sin(a.mul(Int.NONE)));
		if(a.equals(Int.ZERO))
			return Int.ZERO;
		Expr[] pi = MatchForm.linear_form(a, Constant.PI);
		if(pi != null && pi[0].isNumerical() && !pi[0].equals(Int.ZERO))
		{
			Expr c = pi[1];
			Numerical b = (Numerical)pi[0];
			if(c.equals(Int.ZERO))
				return get_sin_value(b);
			return simplify_sin(pi[1]).mul(get_cos_value(b)).add(simplify_cos(pi[1]).mul(get_sin_value(b)));
		}
		if(a.getOperator().equals(Operator.ARCSIN))
			return a.get(0);
		return new Expr(Operator.SIN, a);
	}
	
	public static Expr simplify_cos(Expr a)
	{
		if(is_negative(a))
			return simplify_cos(a.mul(Int.NONE));
		if(a.equals(Int.ZERO))
			return Int.ONE;
		Expr[] pi = MatchForm.linear_form(a, Constant.PI);
		if(pi != null && pi[0].isNumerical() && !pi[0].equals(Int.ZERO))
		{
			Expr c = pi[1];
			Numerical b = (Numerical)pi[0];
			if(c.equals(Int.ZERO))
				return get_cos_value(b);
			return simplify_cos(pi[1]).mul(get_cos_value(b)).add(simplify_sin(pi[1]).mul(get_sin_value(b)));
		}
		if(a.getOperator().equals(Operator.ARCCOS))
			return a.get(0);
		return new Expr(Operator.COS, a);
	}
	
	public static Expr simplify_tan(Expr a)
	{
		if(is_negative(a))
			return Int.NONE.mul(simplify_tan(a.mul(Int.NONE)));
		if(a.equals(Int.ZERO))
			return Int.ZERO;
		Expr[] pi = MatchForm.linear_form(a, Constant.PI);
		if(pi != null && pi[0].isNumerical() && !pi[0].equals(Int.ZERO))
		{
			Expr c = pi[1];
			Numerical b = (Numerical)pi[0];
			if(c.equals(Int.ZERO))
				return get_tan_value(b);
		}
		if(a.getOperator().equals(Operator.ARCTAN))
			return a.get(0);
		return new Expr(Operator.TAN, a);
	}
	
	public static boolean is_negative(Expr a)
	{
		if(a.isNumerical())
			return ((Numerical)a).compareTo(Int.ZERO) < 0;
		if(a.isProduct())
		{
			if(a.get(0).isNumerical())
				return ((Numerical)a.get(0)).compareTo(Int.ZERO) < 0;
		}
		if(a.isSum())
		{
			return is_negative(a.get(0));
		}
		return false;
	}
	
	public static Numerical reduce_modulo_2_pi(Numerical b)
	{
		
		Int d = b.div(Int.TWO).floor();
		b = b.sub(d.mul(Int.TWO));
		return b;
	}
	
	public static Expr get_sin_value(Numerical b)
	{
		b = reduce_modulo_2_pi(b);
		Int sign = Int.ONE;
		//b in [0, 2)
		if(b.compareTo(Int.ONE) >= 0)
		{
			b = b.sub(Int.ONE);
			sign = Int.NONE;
		}
		//b in [0, 1)
		if(b.compareTo(Rational.HALF) > 0)
			b = Int.ONE.sub(b);
		//b in [0, 1/2]
		for(int i = 0;i<sin_pi_values.length;i++)
		{
			if(sin_pi_values[i][0].equals(b))
			    return sign.mul(sin_pi_values[i][1]);
		}
		if(sign.equals(Int.ONE))
			return new Expr(Operator.SIN, b.mul(Constant.PI));
		return new Expr(Operator.MULTIPLY, Int.NONE, new Expr(Operator.SIN, b.mul(Constant.PI)));
	}
	
	public static Expr get_cos_value(Numerical b)
	{
		b = reduce_modulo_2_pi(b);
		Int sign = Int.ONE;
		if(b.compareTo(Int.ONE) >= 0)
		{
			b = b.sub(Int.ONE);
			sign = Int.NONE;
		}
		if(b.compareTo(Rational.HALF) > 0)
		{
			b = Int.ONE.sub(b);
			sign  = sign.mul(Int.NONE);
		}
		Numerical c = b.add(Rational.HALF);
		if(c.compareTo(Rational.HALF) > 0)
			c = Int.ONE.sub(c);
		for(int i = 0;i<sin_pi_values.length;i++)
		{
			if(sin_pi_values[i][0].equals(c))
			    return sign.mul(sin_pi_values[i][1]);
		}
		if(sign.equals(Int.ONE))
			return new Expr(Operator.COS, b.mul(Constant.PI));
		return new Expr(Operator.MULTIPLY, Int.NONE, new Expr(Operator.COS, b.mul(Constant.PI)));
	}

	public static Expr get_tan_value(Numerical b)
	{
		b = reduce_modulo_2_pi(b);
		Int sign = Int.ONE;
		if(b.compareTo(Int.ONE) >= 0)
		{
			b = b.sub(Int.ONE);
			sign = Int.NONE;
		}
		if(b.compareTo(Rational.HALF) > 0)
		{
			b = Int.ONE.sub(b);
			sign  = sign.mul(Int.NONE);
		}
		Expr c = get_sin_value(b);
		Expr d = get_cos_value(b);
		Expr f = c.div(d);
		if(d.equals(Int.ZERO))
			return Constant.UNDEFINED;
		if(AlgebraicNumberField.is_explicit_algebraic_number(f))
			return f;
		if(sign.equals(Int.ONE))
			return new Expr(Operator.TAN, b.mul(Constant.PI));
		return new Expr(Operator.MULTIPLY, Int.NONE, new Expr(Operator.TAN, b.mul(Constant.PI)));
	}
	
	public static Expr simplify_arcsin(Expr a)
	{
		if(is_negative(a))
			return Int.NONE.mul(simplify_arcsin(a.mul(Int.NONE)));
		
		for(int i = 0;i<arcsin_values.length;i++)
			if(arcsin_values[i][0].equals(a))
				return arcsin_values[i][1];
		
		return new Expr(Operator.ARCSIN, a);
	}
	
	public static Expr simplify_arccos(Expr a)
	{
		if(is_negative(a))
			return simplify_arcsin(a.mul(Int.NONE)).add(Constant.PI.div(Int.TWO));
		
		for(int i = 0;i<arccos_values.length;i++)
			if(arccos_values[i][0].equals(a))
				return arccos_values[i][1];
		
		return new Expr(Operator.ARCCOS, a);
	}
	
	public static Expr simplify_arctan(Expr a)
	{
		if(is_negative(a))
			return Int.NONE.mul(simplify_arctan(a.mul(Int.NONE)));
		
		for(int i = 0;i<arctan_values.length;i++)
			if(arctan_values[i][0].equals(a))
				return arctan_values[i][1];
		
		return new Expr(Operator.ARCTAN, a);
	}
}
