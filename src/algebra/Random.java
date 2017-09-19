package algebra;

import Expression.Expr;
import Symbolic.Int;
import Symbolic.Numerical;

public class Random 
{
    public static Int randomInteger(Int a, Int b)
    {
    	return Int.random_int(a, b);
    }
    
    public static Numerical randomExactNumerical(Int a, Int b, Int d)
    {
    	Int q = randomInteger(Int.ONE, d);
    	Int p = randomInteger(a.mul(d), b.mul(d));
    	return p.div(q);
    }
    
    public static Expr randomUnivariateIntegerPoly(Int deg, Int a, Int b, Expr x)
    {
    	Int s = randomInteger(a, b);
    	while(s.equals(Int.ZERO))
    		s = randomInteger(a, b);
    	Expr p = s.mul(x.pow(deg));
    	for(Int i = Int.ZERO;i.compareTo(deg)<0;i = i.add(Int.ONE))
    		p = p.add(randomInteger(a, b).mul(x.pow(i)));
    	return p;
    }
    
    
}
