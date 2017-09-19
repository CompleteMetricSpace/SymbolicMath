package numerical;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.Vector;

import org.apfloat.Apfloat;

import Symbolic.Decimal;
import Symbolic.Int;
import Symbolic.Numerical;
import Symbolic.Rational;

public class NumberIdentification 
{
    public static Int[] continued_fraction(Numerical x)
    {
    	Vector<Int> b = new Vector<Int>();
    	Numerical alpha = x;
    	while(!alpha.frac().equals(Int.ZERO))
    	{
    		b.add(alpha.floor());
    		alpha = Int.ONE.div(alpha.sub(b.lastElement()));
    	}
    	b.add((Int)alpha);
    	return b.toArray(new Int[b.size()]);
    }
    
    public static void main(String[] args)
    {
    	System.out.println("N "+Arrays.deepToString(continued_fraction(new Rational(new Int("588235294"),new Int("10000000000")))));
    }
}
