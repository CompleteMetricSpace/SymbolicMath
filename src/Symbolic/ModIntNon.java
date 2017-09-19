package Symbolic;

public class ModIntNon extends Symbolic
{
	Int integer;
	Int modulus;

	public ModIntNon(Int s, Int p) 
	{
		integer = s.mod(p);
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
	
	public boolean equals(ModIntNon b)
	{
		if(!b.getModulus().equals(modulus))
			return false;
		return integer.sub(b.toInt()).mod(modulus).equals(Int.ZERO);
	}
	

	
	public ModIntNon add(ModIntNon b)
	{
		if(!b.getModulus().equals(this.getModulus()))
			return null;
		return new ModIntNon(this.toInt().add(b.toInt()), modulus);
	}
	
	public ModIntNon sub(ModIntNon b)
	{
		if(!b.getModulus().equals(this.getModulus()))
			return null;
		return new ModIntNon(this.toInt().sub(b.toInt()), modulus);
	}
	
	public ModIntNon mul(ModIntNon b)
	{
		if(!b.getModulus().equals(this.getModulus()))
			return null;
		return new ModIntNon(this.toInt().mul(b.toInt()), modulus);
	}
	
	public ModIntNon div(ModIntNon b)
	{
		if(!b.getModulus().equals(this.getModulus()))
			return null;
		return new ModIntNon(b.toInt().modInverse(modulus), modulus).mul(this);
	}
	
	public ModIntNon power(Int n)
	{
		if(n.equals(Int.ZERO))
			return new ModIntNon(Int.ONE, modulus);
	    if(n.isPositive())	
	    {
	    	ModIntNon m = new ModIntNon(Int.ONE, modulus);
	    	for(Int k = Int.ZERO;k.compareTo(n)<0;k = k.add(Int.ONE))
	    		m = m.mul(this);
	    	return m;
	    }
	    else
	    {
	    	n = n.mul(Int.NONE);
	    	ModIntNon m = new ModIntNon(Int.ONE, modulus);
	    	for(Int k = Int.ZERO;k.compareTo(n)<0;k = k.add(Int.ONE))
	    		m = m.mul(this);
	    	return m.inverse();
	    }
	}
	
	public ModIntNon inverse()
	{
		return new ModIntNon(this.toInt().modInverse(modulus), modulus);
	}
	
	public String toString()
	{
		return "nmodi("+integer+", "+modulus+")";
	}
}
