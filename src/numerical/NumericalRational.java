package numerical;

import Symbolic.Int;
import Symbolic.Numerical;

public class NumericalRational 
{
	public static boolean equal(Numerical a, Numerical b, Int p)
	{
		if(a.sub(b).abs().compareTo(Int.TEN.pow(p.mul(Int.NONE))) <= 0)
			return true;
		return false;
	}
    
	public static Numerical exp(Numerical x, Int p)
	{
		Int n = Int.ZERO;
		while(x.abs().compareTo(Int.TWO) > 0)
		{
			x = x.div(Int.TWO);
			n = n.add(Int.ONE);
		}
		p = (Int) p.add(Int.TWO.pow(n));
		Numerical sum = Int.ZERO;
		Numerical old_sum;
		Numerical term = Int.ONE;
		Int k = Int.ONE;
		do
		{
			old_sum = sum;
			sum = sum.add(term);
			term = term.mul(x.div(k));
			k = k.add(Int.ONE);
		}
		while(!equal(sum, old_sum, p));
		return sum.pow((Int)Int.TWO.pow(n));
	}
	
	public static Numerical root(Numerical x, Int k, Int p)
	{
		Numerical x_n = Int.TEN;
		Numerical old = Int.NONE;
		while(!equal(x_n, old, p))
		{
			old = x_n;
			Numerical pow_k_one = x_n.pow(k.sub(Int.ONE));
			Numerical pow_k = pow_k_one.mul(x_n);
			x_n = x_n.sub(pow_k.sub(x).div(k.mul(pow_k_one)));
		}
		return x_n;
	}
}
