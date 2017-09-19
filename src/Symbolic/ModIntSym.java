package Symbolic;

import java.math.BigInteger;

import Expression.Expr;

public class ModIntSym extends Symbolic
{
	Int integer;
	Int modulus;

	public ModIntSym(Int s, Int p) 
	{
		integer = s.mod(p).symmetric(p);
		modulus = p;
	}

	public Int toInt()
	{
		return integer;
	}
	
	public Int getModulus()
	{
		return modulus;
	}
	
	public boolean equals(ModIntSym b)
	{
		if(!b.getModulus().equals(modulus))
			return false;
		return integer.sub(b.toInt()).mod(modulus).symmetric(modulus).equals(Int.ZERO);
	}
	

	
	public ModIntSym add(ModIntSym b)
	{
		if(!b.getModulus().equals(this.getModulus()))
			return null;
		return new ModIntSym(this.toInt().add(b.toInt()), modulus);
	}
	
	public ModIntSym sub(ModIntSym b)
	{
		if(!b.getModulus().equals(this.getModulus()))
			return null;
		return new ModIntSym(this.toInt().sub(b.toInt()), modulus);
	}
	
	public ModIntSym mul(ModIntSym b)
	{
		if(!b.getModulus().equals(this.getModulus()))
			return null;
		return new ModIntSym(this.toInt().mul(b.toInt()), modulus);
	}
	
	public ModIntSym div(ModIntSym b)
	{
		if(!b.getModulus().equals(this.getModulus()))
			return null;
		return new ModIntSym(b.toInt().modInverse(modulus), modulus).mul(this);
	}
	
	public ModIntSym power(Int n)
	{
		if(n.equals(Int.ZERO))
			return new ModIntSym(Int.ONE, modulus);
	    if(n.isPositive())	
	    {
	    	ModIntSym m = new ModIntSym(Int.ONE, modulus);
	    	for(Int k = Int.ZERO;k.compareTo(n)<0;k = k.add(Int.ONE))
	    		m = m.mul(this);
	    	return m;
	    }
	    else
	    {
	    	n = n.mul(Int.NONE);
	    	ModIntSym m = new ModIntSym(Int.ONE, modulus);
	    	for(Int k = Int.ZERO;k.compareTo(n)<0;k = k.add(Int.ONE))
	    		m = m.mul(this);
	    	return m.inverse();
	    }
	}
	
	public ModIntSym inverse()
	{
		return new ModIntSym(this.toInt().modInverse(modulus), modulus);
	}
	
	public String toString()
	{
		return "smodi("+integer+", "+modulus+")";
	}
	
	

	
}
