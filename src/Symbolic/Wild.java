package Symbolic;

import java.io.Serializable;


public class Wild extends Var
{

	public Wild(String name)
	{
		super(name);
	}
    
	public String toString()
	{
		return name;
	}
}
