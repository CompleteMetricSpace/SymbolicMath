package algebra;

import java.util.Vector;

import Expression.Expr;
import Simplification.Set;
import Symbolic.Int;

//Class for computation with generalized power series with real exponents.
//TODO: Find inversion formula for such a series!
public class RealSeries 
{
    Expr[][] ce;
    
    public RealSeries(Expr[][] exp)
    {
    	ce = new Expr[exp.length][2];
    	for(int i = 0;i<exp.length;i++)
    	{
    	    ce[i][0] = exp[i][0];
    	    ce[i][1] = exp[i][1];
    	}
    }
    
    public Expr getCoef(Expr a)
    {
    	for(int i = 0;i<ce.length;i++)
    	{
    		if(ce[i][1].equals(a))
    			return ce[i][0];
    	}
    	return Int.ZERO;
    }
    
    public Expr[][] getCoefs()
    {
    	Expr[][] e = new Expr[ce.length][2];
    	for(int i = 0;i<ce.length;i++)
    	{
    	    e[i][0] = ce[i][0];
    	    e[i][1] = ce[i][1];
    	}
    	return e;
    }
    
    public RealSeries add(RealSeries b)
    {
    	if(this.isEmpty())
    		return b;
    	if(b.isEmpty())
    		return this;
    	Expr[] A = this.lt();
    	Expr[] B = b.lt();
    	RealSeries d = this.rest().add(b.rest());
    	if(A[1].equals(B[1]))
    		return new RealSeries(Set.add(new Expr[][]{{A[0].add(B[0]), A[1]}}, d.getCoefs()));
    	else
    		return new RealSeries(Set.add(new Expr[][]{A, B}, d.getCoefs()));
    }
    
    public boolean isEmpty()
    {
    	return ce.length == 0;
    }
    
    public Expr[] lt()
    {
    	return ce[0];
    }
    
    public RealSeries rest()
    {
    	Expr[][] c = Set.complement(ce, new Expr[][]{this.lt()});
    	return new RealSeries(c);
    }
    
}
