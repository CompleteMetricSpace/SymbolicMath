package Symbolic;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;

import Expression.Expr;


public class Numerical extends Symbolic
{

	
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
	
	public Numerical make_normal()
	{
		if(this.isRational())
		{
			Rational b = ((Rational)this).normal();
			if(b.getDenominator().equals(Int.ONE))
				return b.getNumerator();
		}
		if(this.isDecimal())
		{
			Decimal c = (Decimal)this;
			c = new Decimal(c.toBigDecimal().stripTrailingZeros());
			try
			{
			    BigInteger s = ((Decimal)c).toBigDecimal().toBigIntegerExact();
			    if(s.compareTo(BigInteger.ZERO) == 0)
			        return new Int(s);
			}
			catch(ArithmeticException e){};
			return c;
		}
		return this;
	}
	
	public Numerical add(Numerical b)
	{
		if(this.isDecimal() && b.isDecimal())
			return ((Decimal)this).add((Decimal)b).make_normal();
		if(this.isRational() && b.isRational())
			return ((Numerical)((Rational)this).add((Rational)b)).make_normal();
		if(this.isInt() && b.isRational())
			return ((Numerical)((Rational)b).add((Int)this)).make_normal();
		if(this.isRational() && b.isInt())
			return ((Numerical)((Rational)this).add((Int)b)).make_normal();
		if(this.isInt() && b.isInt())
			return ((Numerical)((Int)this).add((Int)b)).make_normal();
		if(this.isDecimal())
			return ((Decimal)this).add(b.toDecimal()).make_normal();
		if(b.isDecimal())
			return ((Decimal)b).add(this.toDecimal()).make_normal();
		return null;
	}
	
	public Numerical sub(Numerical b)
	{
		if(this.isDecimal() && b.isDecimal())
			return ((Decimal)this).sub((Decimal)b).make_normal();
		if(this.isRational() && b.isRational())
			return ((Numerical)((Rational)this).sub((Rational)b)).make_normal();
		if(this.isInt() && b.isRational())
			return ((Numerical)((Rational)b).mul(Int.NONE).add((Int)this)).make_normal();
		if(this.isRational() && b.isInt())
			return ((Numerical)((Rational)this).sub((Int)b)).make_normal();
		if(this.isInt() && b.isInt())
			return ((Numerical)((Int)this).sub((Int)b)).make_normal();
		if(this.isDecimal())
			return ((Decimal)this).sub(b.toDecimal()).make_normal();
		if(b.isDecimal())
			return this.toDecimal().sub((Decimal)b).make_normal();
		return null;
	}
	
	public Numerical mul(Numerical b)
	{
		if(this.isRational() && b.isRational())
			return ((Numerical)((Rational)this).mul((Rational)b)).make_normal();
		if(this.isInt() && b.isRational())
			return ((Numerical)((Rational)b).mul((Int)this)).make_normal();
		if(this.isRational() && b.isInt())
			return ((Numerical)((Rational)this).mul((Int)b)).make_normal();
		if(this.isInt() && b.isInt())
			return ((Numerical)((Int)this).mul((Int)b)).make_normal();
		if(this.isDecimal() && b.isDecimal())
			return ((Decimal)this).mul((Decimal)b).make_normal();
		if(this.isDecimal())
			return ((Decimal)this).mul(b.toDecimal()).make_normal();
		if(b.isDecimal())
			return ((Decimal)b).mul(this.toDecimal()).make_normal();
		return null;
	}
	
	public Numerical div(Numerical b)
	{
		if(this.isRational() && b.isRational())
			return ((Numerical)((Rational)this).div((Rational)b)).make_normal();
		if(this.isInt() && b.isRational())
			return ((Numerical)(new Rational((Int)this, Int.ONE)).div(b)).make_normal();
		if(this.isRational() && b.isInt())
			return ((Numerical)(this).div(new Rational((Int)b, Int.ONE))).make_normal();
		if(this.isInt() && b.isInt())
			return new Rational((Int)this, (Int)b).make_normal();
		if(this.isDecimal() && b.isDecimal())
			return ((Decimal)this).div((Decimal)b).make_normal();
		if(this.isDecimal())
			return ((Decimal)this).div(b.toDecimal()).make_normal();
		if(b.isDecimal())
		    return this.toDecimal().div(b).make_normal();
		return null;
	}

	public int compareTo(Numerical b)
	{
		if(this.isRational() && b.isRational())
			return ((Rational)this).compareTo((Rational)b);
		if(this.isInt() && b.isRational())
			return (new Rational((Int)this)).compareTo((Rational)b);
		if(this.isRational() && b.isInt())
			return  ((Rational)this).compareTo(new Rational((Int)b));
		if(this.isInt() && b.isInt())
			return ((Int)this).compareTo((Int)b);
		if(this.isDecimal() && b.isDecimal())
			return ((Decimal)this).compareTo((Decimal)b);
		if(this.isDecimal())
			return ((Decimal)this).compareTo(b.toDecimal());
		if(b.isDecimal())
			return -((Decimal)b).compareTo(this.toDecimal());
		return this.compareTo(b);
	}
	
	
	public Numerical pow(Int n)
	{
		if(n.compareTo(Int.ZERO)<0)
			return Int.ONE.div(this).pow(n.mul(Int.NONE));
		if(n.equals(Int.ZERO))
			return Int.ONE;
		if(n.equals(Int.ONE))
			return this;
		if(n.isOdd())
			return this.mul(this.mul(this).pow(n.sub(Int.ONE).divide(Int.TWO)));
		else
			return this.mul(this).pow(n.divide(Int.TWO));
	}
	
	public Numerical abs() 
	{
		return this.compareTo(Int.ZERO) >= 0?this:this.mul(Int.NONE);
	}
	

	//Complex Number multiplication
	public static Numerical[] mul(Numerical[] a, Numerical[] b)
	{
		return new Numerical[]{a[0].mul(b[0]).sub(a[1].mul(b[1])), a[0].mul(b[1]).add(a[1].mul(b[0]))};
	}
	
	public static Numerical[] add(Numerical[] a, Numerical[] b)
	{
		return new Numerical[]{(Numerical)a[0].add(b[0]),(Numerical) a[1].add(b[1])};
	}
	
	public static Numerical[] sub(Numerical[] a, Numerical[] b)
	{
		return new Numerical[]{(Numerical)a[0].sub(b[0]),(Numerical) a[1].sub(b[1])};
	}
	
	public static Numerical[] div(Numerical[] a, Numerical[] b)
	{
		Numerical k = (Numerical)b[0].mul(b[0]).add(b[1].mul(b[1]));
		return new Numerical[]{(Numerical)a[0].mul(b[0]).add(a[1].mul(b[1])).div(k),(Numerical) a[1].mul(b[0]).sub(a[0].mul(b[1])).div(k)};
	}
	
	public static Numerical[] pow(Numerical[] a, Int b)
	{
		Numerical[] product = new Numerical[]{Int.ONE, Int.ZERO};
		for(Int i = Int.ZERO;i.compareTo(b)<0;i = i.add(Int.ONE))
			product = mul(product, a);
		return product;
	}
	
	public Int floor()
	{
		if(this.isInt())
			return (Int)this;
		else
		{
			if(this.isDecimal())
				return ((Decimal)this).floor();
			Int n = ((Rational)this).getNumerator();
			Int d = ((Rational)this).getDenominator();
			if(n.isNegative())
				return n.divide(d).sub(Int.ONE);
			return n.divide(d);
		}
	}

	public String toDecimalString(int n)
	{
		if(this.isInt())
			return this.toString();
		if(this.isRational())
		{
			BigDecimal s = new BigDecimal(((Rational)this).getNumerator().toBigInteger());
			BigDecimal p = new BigDecimal(((Rational)this).getDenominator().toBigInteger());
			return (s.divide(p, n, BigDecimal.ROUND_FLOOR)).toPlainString();
		}
		return this.toString();
	}
	
	public Decimal toDecimal()
	{
		if(this.isInt())
		{
			return new Decimal(new BigDecimal(((Int)this).toBigInteger()));
		}
		if(this.isRational())
		{
			BigDecimal a = new BigDecimal(((Rational)this).getNumerator().toBigInteger());
			BigDecimal b = new BigDecimal(((Rational)this).getDenominator().toBigInteger());
			return new Decimal(a.divide(b, Decimal.DEFAULT_PRECISION, BigDecimal.ROUND_HALF_UP));
		}
		if(this.isDecimal())
		{
			BigDecimal c = ((Decimal)this).toBigDecimal();
			c.setScale(Decimal.DEFAULT_PRECISION, BigDecimal.ROUND_HALF_UP);
			return new Decimal(c);
		}
		return null;
	}
	
	public Numerical toExactNumerical()
	{
		if(this.isRational() || this.isInt())
			return this;
		if(this.isDecimal())
		    return ((Decimal)this).toRational();
		return this;
	}

	public Numerical frac() 
	{
		return this.sub(this.floor());
	}
	
}
