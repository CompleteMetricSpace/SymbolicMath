package Symbolic;


public class Literal extends Var
{

	public Literal(String name) 
	{
		super(name);
	}

	public String toString()
	{
		return name;
	}
}
