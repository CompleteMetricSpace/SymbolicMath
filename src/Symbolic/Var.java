package Symbolic;

import java.io.Serializable;



public class Var extends Symbolic
{
    String name;
    
    public Var(String name)
    {
    	this.name = name;
    }
    
    public boolean equals(Var b)
    {
    	return name.equals(b.getName());
    }

	public String getName() 
	{
		return name;
	}
	
	public String toString() 
	{
		return name;
	}
}
