package solve;

import algebra.Algebra;
import polynomial.Factor;
import polynomial.Poly;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Symbolic.Int;

public class Solve
{
    public static Expr[] solve(Expr f, Expr x)
    {    	
    	Expr r = Int.ZERO;
    	while(true)
    	{
    		if(Poly.is_poly(f, x))
        	    return PolySolve.solve_polynomial(f.sub(r), x);
            Expr[] nd = Algebra.NumeratorDenominator(f);
            if(!nd[1].equals(Int.ONE) && r.equals(Int.ZERO))
            	return solve(nd[0], x);
    		if(f.isProduct() && r.equals(Int.ZERO))
    		{
    			Expr[] sol = new Expr[]{};
    			for(int i = 0;i<f.length();i++)
    			{
    				Expr[] s = solve(f.get(i), x);
    				sol = Set.union(sol, s);
    			}
    			return sol;
    		}
    		if(f.equals(x))
    			return new Expr[]{r};
    		if(f.isSymbolic())
    			return new Expr[]{};
    		int occ = getOccurence(f, x);
    		if(occ == 1)
    		{
    			int k = getIndex(f, x);
    			if(f.isSum())
    			{
    				Expr A = f.sub(f.get(k));
    				r = r.sub(A);
    				f = f.get(k);
    				continue;
    			}
    			if(f.isProduct())
    			{
    				Expr A = f.div(f.get(k));
    				r = r.div(A);
    				f = f.get(k);
    				continue;
    			}
    			if(f.isPower())
    			{
    				if(k == 0)
    				{
    					r = r.pow(Int.ONE.div(f.get(1)));
    					f = f.get(0);
    					continue;
    				}
    				else
    				{
    					r = r.log().div(f.get(0).log());
    					f = f.get(1);
    					continue;
    				}
    			}
    			if(f.getOperator().equals(Operator.EXP))
    			{
    				f = f.get(0);
    				r = r.log();
    				continue;
    			}
    		}
    	    return new Expr[]{};
    	}
    }
    
    public static int getOccurence(Expr u, Expr x)
    {
    	if(u.equals(x))
    	    return 1;
    	if(u.isSymbolic())
    		return 0;
    	int c = 0;
    	for(int i = 0;i<u.length();i++)
    		if(!u.get(i).isFreeOf(x))
    			c++;
    	return c;
    }
    
    public static int getIndex(Expr u, Expr x)
    {
    	if(u.isSymbolic())
    		return -1;
    	for(int i = 0;i<u.length();i++)
    		if(!u.get(i).isFreeOf(x))
    			return i;
    	return -1;
    }


}
