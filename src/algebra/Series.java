package algebra;

import polynomial.Poly;
import Expression.Expr;
import Expression.Operator;
import Simplification.Simplification;
import Symbolic.Int;

public class Series 
{
	public final static Series ONE = new Series(new Expr[]{Int.ONE});
	public final static Series ZERO = new Series(new Expr[]{Int.ZERO});
	
	private Expr[] coefs;
	
	public Series(Expr[] coefs)
	{
	    this.coefs = coefs;
	}
	
	public Series(Expr u, Expr x)
	{
		coefs = poly_to_series(u, x);
	}
	
	public Expr[] getCoefs()
	{
	    Expr[] c = new Expr[coefs.length];
	    for(int i = 0;i<c.length;i++)
	    	c[i] = coefs[i];
	    return c;
	}
	
	public Expr getCoef(int i)
	{
		return coefs[i];
	}
	
	public int getLength()
	{
		return coefs.length;
	}
	
	public Series add(Series b)
	{
		int n = Math.min(this.getLength(), b.getLength());
    	Expr[] c = new Expr[n];
    	for(int i = 0;i<n;i++)
    		c[i] = this.getCoef(i).add(b.getCoef(i));
    	return new Series(c);
	}
	
    public Series mul(Series b)
    {
    	int n = Math.min(this.getLength(), b.getLength());
    	Expr[] c = new Expr[n];
    	for(int i = 0;i<n;i++)
    	{
    		Expr sum = Int.ZERO;
    		for(int j = 0;j<=i;j++)
    			sum = sum.add(this.getCoef(j).mul(b.getCoef(i-j)));
    		c[i] = sum;
    	}
    	return new Series(c);
    }
    
    public Series mul(Expr a)
    {
    	Expr[] c = new Expr[this.getLength()];
    	for(int i = 0;i<c.length;i++)
    		c[i] = coefs[i].mul(a);
    	return new Series(c);
    }
    
    public Series sub(Series b)
    {
    	int n = Math.min(this.getLength(), b.getLength());
    	Expr[] c = new Expr[n];
    	for(int i = 0;i<n;i++)
    		c[i] = this.getCoef(i).sub(b.getCoef(i));
    	return new Series(c);
    }
    
    public Series div(Series b)
    {
    	return this.mul(b.inverse());
    }
    
    public Series inverse()
    {
    	int n = this.getLength();
    	Expr[] c = new Expr[n];
    	if(this.getCoef(0).equals(Int.ZERO))
    		throw new IllegalArgumentException("Can't find inverse for series with first coefficient zero");
    	c[0] = Int.ONE.div(this.getCoef(0));
    	for(int i = 1;i<n;i++)
    	{
    		Expr sum = Int.ZERO;
    		for(int j = 1;j<=i;j++)
    			sum = sum.add(this.getCoef(j).mul(c[i-j]));
    		c[i] = Int.NONE.mul(sum).div(this.getCoef(0));
    	}
    	return new Series(c);
    }
    
    public Series exp()
    {
    	int n = this.getLength();
    	Expr[] c = new Expr[n];
    	c[0] = Simplification.simplify_recursive(new Expr(Operator.EXP, this.getCoef(0)));
    	for(int i = 1;i<n;i++)
    	{
    		Expr sum = Int.ZERO;
    		for(int k = 0;k<=i-1;k++)
    			sum = sum.add(c[k].mul(this.getCoef((i-1)-k+1)).mul(new Int((i-1)-k+1)));
    		c[i] = sum.div(new Int(i));
    	}
    	return new Series(c);
    }
    
    public Series compose(Series b)
    {
    	Series s = ZERO(this.getLength());
    	if(!b.getCoef(0).equals(Int.ZERO))
    		throw new IllegalArgumentException("Can't compose series with first cofficient nonzero");
    	for(int i = 0;i<coefs.length;i++)
    	{
    		s = s.add(b.pow(new Int(i)).mul(coefs[i]));
    	}
    	return s;
    }
    
    /**
     * Power series of log(x+1)
     * @param n - an integer
     * @return power series of log(x+1) up to (n-1)-th order
     */
    public static Series log(int n)
    {
    	if(n == 0)
    		return ZERO;
    	Expr[] c = new Expr[n];
    	c[0] = Int.ZERO;
    	for(int i = 1;i<n;i++)
    	{
    		c[i] = Int.NONE.pow(new Int(i-1)).div(new Int(i));
    	}
    	return new Series(c);
    }
    
    public static Expr[] poly_to_series(Expr u, Expr x)
    {
    	if(u.equals(Int.ZERO))
    		return new Expr[]{Int.ZERO};
    	Int n = Poly.degree(u, x);
    	Expr[] s = new Expr[n.toInt()+1];
    	for(int i = 0;i<=n.toInt();i++)
    		s[i] = Poly.coefficient_poly(u, x, new Int(i));
    	return s;
    }
    
    public Expr to_poly(Expr x)
    {
    	Expr sum = Int.ZERO;
    	for(int i = 0;i<coefs.length;i++)
    		sum = sum.add(coefs[i].mul(x.pow(new Int(i))));
    	return sum;
    }

	public Series pow(Int n)
	{
		if(n.equals(Int.ZERO))
			return ONE(this.getLength());
		if(n.isNegative())
			return this.inverse().pow(n.mul(Int.NONE));
		if(n.isOdd())
			return this.mul(this.mul(this).pow(n.sub(Int.ONE).divide(Int.TWO)));
		else
			return this.mul(this).pow(n.divide(Int.TWO));
	}

	private static Series ONE(int n) 
	{
		Expr[] c = new Expr[n];
		for(int i = 1;i<n;i++)
			c[i] = Int.ZERO;
        c[0] = Int.ONE;
		return new Series(c);
	}
    
	private static Series ZERO(int n) 
	{
		Expr[] c = new Expr[n];
		for(int i = 0;i<n;i++)
			c[i] = Int.ZERO;
		return new Series(c);
	}

	public Series set(Expr a, int k)
	{
		Expr[] c = new Expr[this.getLength()];
		for(int i = 0;i<c.length;i++)
		{
			if(i == k)
				c[i] = a;
			else
				c[i] = coefs[i];
		}
		return new Series(c);
	}
	
	public Series cut(int n)
	{
		Expr[] s = new Expr[n];
		int m = this.getCoefs().length;
		if(n > m)
		{
			for(int i = 0;i<m;i++)
				s[i] = this.getCoef(i);
			for(int i = m;i<n;i++)
				s[i] = Int.ZERO;
			return new Series(s);
		}
		else
		{
			for(int i = 0;i<n;i++)
				s[i] = this.getCoef(i);
			return new Series(s);
		}
	}
	
	public static Series exp_log_series(Expr f, Expr x, int n)
	{
		if(f.isFreeOf(x))
			return new Series(new Expr[]{f}).cut(n);
		if(Poly.is_poly(f, x))
			return new Series(f, x).cut(n);
		if(f.isSum())
		{
			Expr A = f.sub(f.get(0));
			return exp_log_series(f.get(0), x, n).add(exp_log_series(A, x, n));
		}
		if(f.isProduct())
		{
			Expr A = f.div(f.get(0));
			return exp_log_series(f.get(0), x, n).mul(exp_log_series(A, x, n)); 
		}
		if(f.isPower())
		{
			Int k = (Int) f.get(1);
			return exp_log_series(f.get(0), x, n).pow(k);
		}
		if(f.getOperator().equals(Operator.EXP))
		{
			return exp_log_series(f.get(0), x, n).exp();
		}
		if(f.getOperator().equals(Operator.LOG))
		{
			return log(n).compose(exp_log_series(f.get(0), x, n).sub(Series.ONE.cut(n)));
		}
		return null;
	}
    
}
