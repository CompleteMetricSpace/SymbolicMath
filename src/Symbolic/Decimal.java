package Symbolic;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;

public class Decimal extends Numerical
{
	public static int DEFAULT_PRECISION = 20;
    BigDecimal number;	
	
	public Decimal(BigDecimal n) 
	{
		number = n;
	}

	public Decimal add(Decimal b)
	{
		return new Decimal(this.number.add(b.number).setScale(DEFAULT_PRECISION, BigDecimal.ROUND_HALF_UP));
	}
	
	public Decimal mul(Decimal b)
	{
		return new Decimal(this.number.multiply(b.number).setScale(DEFAULT_PRECISION, BigDecimal.ROUND_HALF_UP));
	}
	
	public Decimal sub(Decimal b)
	{
		return new Decimal(this.number.subtract(b.number).setScale(DEFAULT_PRECISION, BigDecimal.ROUND_HALF_UP));
	}
	
	public Decimal div(Decimal b)
	{
		return new Decimal(this.number.divide(b.number, DEFAULT_PRECISION, BigDecimal.ROUND_HALF_UP));
	}
	
	public Numerical toRational()
	{
		return new Int(number.unscaledValue()).div(Int.TEN.pow(new Int(number.scale())));
	}
	
	public Int floor()
	{
		return new Int(number.toBigInteger());
	}
	
	@Override
	public String toString()
	{
		int p = number.precision();
		int sc = number.scale()-number.precision()+1;
		String s = number.scaleByPowerOfTen(sc).setScale(p, BigDecimal.ROUND_HALF_UP).stripTrailingZeros().toPlainString();
		if(s.indexOf(".") == -1)
			s = s+".0";
		if(sc == 0)
			return s;
		else
		{
			if(sc > 0)
			    return s+"*10^("+(-sc)+")";
			else
				return s+"*10^"+(-sc);
		}
	}
	
	public BigDecimal toBigDecimal()
	{
		return number;
	}
	
	public int getPrecision()
	{
		return number.scale();
	}
	
	public int compareTo(Decimal c)
	{
		return this.number.compareTo(c.number);
	}

}
