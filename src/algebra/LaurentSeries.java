package algebra;

import java.util.Vector;

import Expression.Expr;
import Expression.Operator;
import Symbolic.Int;
import Symbolic.Var;

public class LaurentSeries 
{
    Expr[] coefs;
    Int[] exp; 
    Int max;
    
    public LaurentSeries(Expr[] c, Int[] e, Int m)
    {
    	coefs = c;
    	exp = e;
    	max = m;
    }
    
    public Expr[] getCoefs()
    {
    	return coefs;
    }
    
    public Int[] getExponents()
    {
    	return exp;
    }
    
    public Int getMax()
    {
    	return max;
    }
    
    public Expr getCoef(Int n)
    {
    	for(int i = 0;i<exp.length;i++)
    		if(exp[i].equals(n))
    			return coefs[i];
    	return Int.ZERO;
    }
    
    public LaurentSeries mul(Expr a)
    {
    	Expr[] c = new Expr[coefs.length];
    	for(int i = 0;i<coefs.length;i++)
    		c[i] = coefs[i].mul(a);
    	return new LaurentSeries(c, exp, this.getMax());
    }
    
    public LaurentSeries shift(Int n)
    {
    	Int[] e = new Int[exp.length];
    	for(int i = 0;i<exp.length;i++)
    		e[i] = exp[i].add(n);
    	return new LaurentSeries(coefs, e, this.getMax().add(n));
    }
    
    public LaurentSeries substPowOfX(Int n)
    {
    	Int[] e = new Int[exp.length];
    	for(int i = 0;i<exp.length;i++)
    		e[i] = exp[i].mul(n);
    	return new LaurentSeries(coefs, e, this.getMax().mul(n));
    }
    
    public LaurentSeries cleanCoefs()
    {
    	int c = 0;
    	for(int i = 0;i<coefs.length;i++)
    		if(!coefs[i].equals(Int.ZERO))
                c++;
    	Expr[] nc = new Expr[c];
    	Int[] e = new Int[c];
    	c = 0;
    	for(int i = 0;i<coefs.length;i++)
    		if(!coefs[i].equals(Int.ZERO))
    		{
    			nc[c] = coefs[c];
    			e[c] = exp[c];
    			c++;
    		}
    	return new LaurentSeries(nc, e, this.getMax());
    }
    
    //Return null if power series is zero;
    public Int order()
    {
    	if(exp.length == 0)
    		return null;
    	Int n = exp[0];
    	for(int i = 1;i<exp.length;i++)
    		if(exp[i].compareTo(n) < 0)
    			n = exp[i];
    	return n;	
    }
    
    public Int maxExponent()
    {
    	if(exp.length == 0)
    		return null;
    	Int n = exp[0];
    	for(int i = 1;i<exp.length;i++)
    		if(exp[i].compareTo(n) > 0)
    			n = exp[i];
    	return n;	
    }
    
    public boolean isEmpty()
    {
    	return exp.length == 0;
    }
    
    public LaurentSeries add(LaurentSeries b)
    {
    	if(this.isEmpty())
    		return b;
    	if(b.isEmpty())
    		return this;
    	Int m = Int.min(this.order(), b.order());
    	Int new_max = Int.min(this.getMax(), b.getMax());
    	Vector<Expr> c = new Vector<Expr>();
    	Vector<Int> e = new Vector<Int>();
    	for(Int i = m;i.compareTo(new_max)<=0;i = i.add(Int.ONE))
    	{
    		Expr s = this.getCoef(i).add(b.getCoef(i));
    		if(!s.equals(Int.ZERO))
    		{
    			c.add(s);
    			e.add(i);
    		}
    	}
    	return new LaurentSeries(c.toArray(new Expr[c.size()]), e.toArray(new Int[e.size()]),
    			new_max);
    }
    
    public LaurentSeries mul(LaurentSeries b)
    {
    	if(this.isEmpty() || b.isEmpty())
    		return new LaurentSeries(new Expr[]{}, new Int[]{}, Int.min(this.getMax(), b.getMax()));
    	Int m_ = this.order(), n_ = this.maxExponent();
    	Int m = m_.add(b.order());
    	Int new_max = Int.min(this.getMax(), b.getMax());
    	Vector<Expr> c = new Vector<Expr>();
    	Vector<Int> e = new Vector<Int>();
    	for(Int k = m;k.compareTo(new_max)<=0;k = k.add(Int.ONE))
    	{
    		Expr d = Int.ZERO;
    		for(Int i = m_;i.compareTo(n_)<=0;i = i.add(Int.ONE))
    		    d = d.add(this.getCoef(i).mul(b.getCoef(k.sub(i))));
    		if(!d.equals(Int.ZERO))
    		{
    			c.add(d);
    			e.add(k);
    		}
    	}
    	return new LaurentSeries(c.toArray(new Expr[c.size()]), e.toArray(new Int[e.size()]),
    			new_max);
    }
    
    public LaurentSeries inverse()
    {
    	if(this.isEmpty())
    		throw new IllegalArgumentException("Cannot find inverse for zero series");
    	//Factor out x^ord(this)
    	Int m = this.order();
    	LaurentSeries a = this.shift(m.mul(Int.NONE));
    	
    	Vector<Expr> c = new Vector<Expr>();
    	Vector<Int> e = new Vector<Int>();
    	c.add(Int.ONE.div(a.getCoef(Int.ZERO)));
    	e.add(Int.ZERO);
    	for(Int n = Int.ONE;n.compareTo(a.getMax())<=0;n = n.add(Int.ONE))
    	{
    		Expr sum = Int.ZERO;
    		for(Int i = Int.ONE;i.compareTo(n)<=0;i = i.add(Int.ONE))
    		{
    			//Find b_(n-i)
    			Expr b = Int.ZERO;
    			for(int j = 0;j<e.size();j++)
    				if(e.get(j).equals(n.sub(i)))
    					b = c.get(j);
    			sum = sum.add(a.getCoef(i).mul(b));
    		}
    		sum = Int.NONE.div(a.getCoef(Int.ZERO)).mul(sum);
    		if(!sum.equals(Int.ZERO))
    		{
    			c.add(sum);
    			e.add(n);
    		}
    	}
    	//Shift back
    	return new LaurentSeries(c.toArray(new Expr[c.size()]), e.toArray(new Int[e.size()]),
    			this.getMax()).shift(m.mul(Int.NONE));
    }
    
    public LaurentSeries power(Int n)
    {
    	if(n.equals(Int.ZERO))
			return ONE(this.getMax());
		if(n.isNegative())
			return this.inverse().power(n.mul(Int.NONE));
		if(n.isOdd())
			return this.mul(this.mul(this).power(n.sub(Int.ONE).divide(Int.TWO)));
		else
			return this.mul(this).power(n.divide(Int.TWO));
    }
    
    /**
     *  Composition of laurent series using horner method
     * @param b - a laurent series
     * @return The composition b(this)
     */
    public LaurentSeries compose(LaurentSeries b)
    {
    	if(!this.getCoef(Int.ZERO).equals(Int.ZERO))
    		throw new IllegalArgumentException("Can't compose series with non-zero constant term");
    	LaurentSeries s1 = ZERO(this.getMax());
    	LaurentSeries s2 = ZERO(this.getMax());
    	Int n = b.order();
    	Int m = b.maxExponent();
    	//Horner method
    	for(Int i = m;i.compareTo(Int.ZERO)>=0;i = i.sub(Int.ONE))
    	{
    		s1 = s1.mul(this).add(ONE(max).mul(b.getCoef(i)));
    	}
    	if(n.compareTo(Int.ZERO) < 0)
    	{
    		LaurentSeries inv = this.inverse();
    		for(Int i = n;i.compareTo(Int.ZERO)<0;i = i.add(Int.ONE))
        	{
        		s2 = s2.mul(inv).add(ONE(max).mul(b.getCoef(i)));
        	}
    		s2 = s2.mul(inv);
    	}
    	return s1.add(s2);
    }
    
    public static LaurentSeries ZERO(Int n)
    {
        return new LaurentSeries(new Expr[]{}, new Int[]{}, n);	
    }
    
    public static LaurentSeries ONE(Int n)
    {
        return new LaurentSeries(new Expr[]{Int.ONE}, new Int[]{Int.ZERO}, n);	
    }
    
    public static LaurentSeries X(Int n)
    {
        return new LaurentSeries(new Expr[]{Int.ONE}, new Int[]{Int.ONE}, n);	
    }
    
    /**
     * Series of exp(x) = 1 + x + x^2/2 + x^3/6 + ...
     * @param n - a positive integer 
     * @return Series of exp(x) around 0 to n terms.
     */
    public static LaurentSeries exp(Int n)
    {
    	Expr[] c = new Expr[n.toInt()+1];
    	Int[] e = new Int[c.length];
    	Int d = Int.ONE;
    	c[0] = Int.ONE;
    	e[0] = Int.ZERO;
    	for(int i = 1;i<c.length;i++)
    	{
    		d = d.mul(new Int(i));
    		c[i] = Int.ONE.div(d);
    		e[i] = new Int(i);
    	}
    	return new LaurentSeries(c, e, n);
    }
    
    /**
     * Series of log(x+1) = x - x^2/2 + x^3/3 - x^4/4 + ...
     * @param n - a positive integer
     * @return Series expansion of log(x+1) around 0 to n terms.
     */
    public static LaurentSeries log(Int n)
    {
    	Expr[] c = new Expr[n.toInt()];
    	Int[] e = new Int[c.length];
    	for(int i = 1;i<=c.length;i++)
    	{
    		c[i-1] = i%2 == 0?Int.NONE.div(new Int(i)):Int.ONE.div(new Int(i));
    		e[i-1] = new Int(i);
    	}
    	return new LaurentSeries(c, e, n);
    }
    
    public Expr toPoly(Expr x)
    {
    	Expr c = Int.ZERO;
    	for(int i = 0;i<coefs.length;i++)
    		c = c.add(coefs[i].mul(x.pow(exp[i])));
    	return c;
    }

    public static LaurentSeries series(Expr f, Expr x, Int n)
    {
    	if(f.isFreeOf(x))
    		return ONE(n).mul(f);
    	if(f.equals(x))
    		return X(n);
    	if(f.isSum())
    	    return series(f.get(0), x, n).add(series(f.sub(f.get(0)), x, n));
    	if(f.isProduct())
    	    return series(f.get(0), x, n).mul(series(f.div(f.get(0)), x, n));
    	if(f.isPower())
    	    return series(f.get(0), x, n).power((Int)f.get(1));
    	if(f.getOperator().equals(Operator.EXP))
    	{
    		LaurentSeries s = series(f.get(0), x, n);
    		Expr t = s.getCoef(Int.ZERO);
    		return s.add(ONE(n).mul(t.mul(Int.NONE))).compose(exp(n)).mul(t.exp());
    	}
    	if(f.getOperator().equals(Operator.LOG))
    	{
    		LaurentSeries s = series(f.get(0), x, n);
    		Expr t = s.getCoef(Int.ZERO);
    		if(t.equals(Int.ZERO))
    			throw new IllegalArgumentException("Cannot compute series due to logarithm around 0");
    		return X(n).mul(Int.ONE.div(t)).compose(log(n)).add(ONE(n).mul(t.log()));
    	}
    	throw new IllegalArgumentException("Cannot compute series due to unknown function: "+f);
    }
    
}
