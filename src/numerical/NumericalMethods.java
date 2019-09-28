package numerical;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;

import Symbolic.Int;
import Symbolic.Numerical;

public class NumericalMethods 
{
	public static BigDecimal TWO = new BigDecimal("2");
	
	public static boolean equal(BigDecimal a, BigDecimal b, int p)
	{
		if(a.subtract(b).compareTo(a.ulp()) < 0)
			return true;
		return false;
	}
	
	public static BigDecimal power(BigDecimal b, BigInteger n, int p)
	{
		if(n.compareTo(BigInteger.ZERO) < 0)
			return BigDecimal.ONE.divide(power(b, n.negate(), p), new MathContext(p));
		if(n.compareTo(BigInteger.ZERO) == 0)
			return BigDecimal.ONE;
		if(n.mod(new BigInteger("2")).compareTo(BigInteger.ZERO) != 0)
			return b.multiply(power(b.multiply(b, new MathContext(p)), n.subtract(BigInteger.ONE).divide(new BigInteger("2")), p), new MathContext(p));
		else
			return power(b.multiply(b), n.divide(new BigInteger("2")), p).plus(new MathContext(p));
	}
	
	public static BigDecimal exp(BigDecimal x, int p)
	{
		int n = 0;
		
		while(x.abs().compareTo(new BigDecimal("1")) >= 0)
		{
			x = x.movePointLeft(1);
			n = n + 1;
		}
		
		System.out.println("n: "+n+" x: "+x);
		//Increase precision for small number
		p = p+1;
		BigDecimal sum = BigDecimal.ZERO;
		BigDecimal old_sum;
		BigDecimal term = BigDecimal.ONE;
		BigDecimal k = BigDecimal.ONE;
		do
		{
			old_sum = sum;
			sum = sum.add(term, new MathContext(p));
			term = term.multiply(x.divide(k, new MathContext(p)), new MathContext(p));
			System.out.println("term: "+term);
			k = k.add(BigDecimal.ONE);
		}
		while(!equal(sum, old_sum, p));
		System.out.println("sum: "+sum);
		return power(sum, new BigInteger("10").pow(n), p);
	}
	
	public static void main(String[] args)
	{
		BigDecimal a = new BigDecimal("10000.00");
		BigDecimal exp = exp(a, 100);
		System.out.println("exp: "+exp);
	}
	
	
	
}
