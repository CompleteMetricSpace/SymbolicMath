package polynomial;

import java.util.Vector;

import Expression.Expr;
import Simplification.Simplification;
import Symbolic.Int;
import Symbolic.Var;

public class MVPoly
{
    Int[][] pow;
    Expr[] coef;
    Var[] var;
    
    public MVPoly(Var[] vars, Expr[] coefs, Int[][] pows)
    {
    	pow = pows;
    	coef = coefs;
    	var = vars;
    }
    
    public static MVPoly ONE(Var[] vars)
    {
    	return new MVPoly(vars, new Expr[]{Int.ONE}, new Int[][]{getIntList(Int.ZERO, vars.length)});
    }
    
    public static MVPoly ZERO(Var[] vars)
    {
    	return new MVPoly(vars, new Expr[]{Int.ZERO}, new Int[][]{getIntList(Int.ZERO, vars.length)});
    }
    
    public static MVPoly Int(Var[] vars, Int a)
    {
    	return new MVPoly(vars, new Expr[]{a}, new Int[][]{getIntList(Int.ZERO, vars.length)});
    }
    
    public static MVPoly X(Var[] vars, int i)
    {
    	return new MVPoly(vars, new Expr[]{Int.ONE}, new Int[][]{getIntList(Int.ONE, vars.length, i)});
    }
    
    public MVPoly(Expr u, Var[] vars)
    {
    	if(!u.isSum())
    	{
    		Expr[][] monomial = Poly.coefficient_monomial(u, vars);
    		pow = new Int[1][];
    		pow[0] = Simplification.castToInt(monomial[1]);
    		coef = new Expr[]{monomial[0][0]};
    		var = vars;
    	}
    	else
    	{
    		Vector<Int[]> powers = new Vector<>();
    		Vector<Expr> coefficients = new Vector<>();
    		for(int i = 0;i<u.length();i++)
    		{
    			Expr[][] monomial = Poly.coefficient_monomial(u.get(i), vars);	
    			Int[] k = Simplification.castToInt(monomial[1]);
    			boolean has_pow = false;
    			for(int j = 0;j<powers.size();j++)
    			{
    				
    				if(equal(powers.get(j), k))
    				{
    					has_pow = true;
    					coefficients.set(j, coefficients.get(j).add(monomial[0][0]));
    				}
    			}
    			if(!has_pow)
    			{
    				powers.add(k);
    				coefficients.add(monomial[0][0]);
    			}
    		}
    		var = vars;
    		coef = coefficients.toArray(new Expr[coefficients.size()]);
    		pow = powers.toArray(new Int[powers.size()][]);
    	}
    }
    
    public String toString()
    {
    	String s = "";
    	for(int i = 0;i<coef.length;i++)
    	{
    		String c = coef[i].toString();
    		for(int j = 0;j<var.length;j++)
    		{
    			c += "*"+var[j]+"^"+pow[i][j];
    		}
    		if(i != 0)
    		    s += "+("+c+")";
    		else
    			s += "("+c+")";
    	}
    	return s;
    }
  
    
    
    
    
    static Int[] getIntList(Int n, int length)
    {
    	Int[] j = new Int[length];
    	for(int i = 0;i<length;i++)
    		j[i] = n;
    	return j;
    }
    
    public static Int[] getIntList(Int n, int length, int index)
    {
    	Int[] j = new Int[length];
    	for(int i = 0;i<length;i++)
    		j[i] = Int.ZERO;
    	j[index] = n;
    	return j;
    }
    
    public static boolean equal(Int[] a, Int[] b)
    {
    	if(a.length != b.length)
    		return false;
    	for(int i = 0;i<a.length;i++)
    	{
    		if(!a[i].equals(b[i]))
    			return false;
    	}
    	return true;
    }
    
   
}
