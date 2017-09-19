package Symbolic;

public class Str extends Symbolic
{
    String str;
    
    public Str(String s)
    {
    	str = s;
    }
    
    public String toString()
    {
    	return "\""+str+"\"";
    }
    
    public String getString()
    {
    	return str;
    }
    
    public boolean equals(Str b)
    {
    	return this.str.equals(b.str);
    }
	
}
