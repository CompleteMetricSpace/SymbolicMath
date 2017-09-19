package algebra;

import java.util.HashMap;
import java.util.function.BiFunction;
import java.util.function.Function;

import Expression.Expr;
import Expression.Parser;
import Symbolic.Int;

/**
 * 
 * @author KhAKhA
 * Power Series with lazy evaluation 
 */
public class PowerSeries
{
    private Function<Long, Expr> f;
    private HashMap<Long, Expr> vals;

    public PowerSeries(Function<Long, Expr> f)
    {
	this.f = f;
	vals = new HashMap<>();
    }
    
    public PowerSeries(Function<Long, Expr> f, HashMap<Long, Expr> map)
    {
	this.f = f;
	vals = map;
    }

    public Expr getCoef(Long k)
    {
	if(vals.containsKey(k))
	    return vals.get(k);
	Expr c = f.apply(k);
	vals.put(k, c);
	return c;
    }

    public boolean isInvertible()
    {
	return !getCoef(0L).equals(Int.ZERO);
    }
    
    public long getNumberOfEvaluatedCoefs()
    {
	return vals.size();
    }

    public PowerSeries add(PowerSeries b)
    {
	return new PowerSeries(n -> this.getCoef(n).add(b.getCoef(n)));
    }

    public PowerSeries sub(PowerSeries b)
    {
	return new PowerSeries(n -> this.getCoef(n).sub(b.getCoef(n)));
    }

    public PowerSeries mul(PowerSeries b)
    {
	Function<Long, Expr> g = k -> {
	    Expr sum = Int.ZERO;
	    for(Long i = 0L;i<=k;i++)
		sum = sum.add(this.getCoef(i).mul(b.getCoef(k-i)));
	    return sum;
	};
	return new PowerSeries(g);
    }
    
    public PowerSeries add(Expr b)
    {
	return new PowerSeries(n -> n==0L?this.getCoef(n).add(b):this.getCoef(n));
    }

    public PowerSeries sub(Expr b)
    {
	return new PowerSeries(n -> n==0L?this.getCoef(n).sub(b):this.getCoef(n));
    }

    public PowerSeries mul(Expr b)
    {
	return new PowerSeries(n -> this.getCoef(n).mul(b));
    }
    
    public PowerSeries invert()
    {
	if(!isInvertible())
	    throw new IllegalStateException("PowerSeries cannot be inverted");
	Expr a = this.getCoef(0L).pow(Int.NONE);
	HashMap<Long, Expr> bTable = new HashMap<>();
	bTable.put(0L, a);
	BiFunction<BiFunction, Long, Expr> g = (s, k) -> {
	    if(bTable.containsKey(k))
		return bTable.get(k);
	    Expr sum = Int.ZERO;
	    for(Long n =0L;n<k;n++)
		sum = sum.add(this.getCoef(k-n).mul((Expr)s.apply(s, n)));
	    Expr b = sum.mul(a.mul(Int.NONE));
	    bTable.put(k, b);
	    return b;
	};
	Function<Long, Expr> h = k -> g.apply(g, k);
	return new PowerSeries(h, bTable);
    }
    
    public String toString(Long k)
    {
	String s = "[";
	Long i = 0L;
	while(i.compareTo(k)<0)
	{
	    s += this.getCoef(i)+", ";
	    i++;
	}
	s+= this.getCoef(k)+"]";
	return s;
    }
    
    public static void main(String[] args)
    {
	Function<Long, Expr> g = n -> Parser.build("a+b").pow(new Int(n));
	PowerSeries ps = new PowerSeries(g);
	PowerSeries psi = ps.invert();
	//ArrayList<Integer> list = new ArrayList<>();
	//list.set(5, 1);
	System.out.println(ps.toString(10L));
	System.out.println(psi.toString(10L));
	System.out.println(ps.mul(psi).toString(10L));
	System.out.println(psi.getNumberOfEvaluatedCoefs());
	System.out.println(ps.getNumberOfEvaluatedCoefs());
	System.out.println(psi.vals.keySet());
	System.out.println(ps.vals.keySet());
	
    }

}
