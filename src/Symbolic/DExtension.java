package Symbolic;

import Expression.Expr;

public class DExtension extends Var
{
	String type;
	Expr arg;
    public DExtension(String name, String type, Expr arg)
    {
    	super(name);
    	this.type = type;
    	this.arg = arg;
    }
    
    public Expr getArg()
    {
    	return arg;
    }
    
    public String getType()
    {
    	return type;
    }
    
    public boolean isLog()
    {
    	return type.equals("LOG");
    }
    
    public boolean isExp()
    {
    	return type.equals("EXP");
    }
    
    public boolean isX()
    {
    	return type.equals("X");
    }
    
    public boolean equals(DExtension b)
    {
    	return this.getName().equals(b.getName()) && this.getType().endsWith(b.getType()) && this.getArg().equals(b.getArg());
    }
    
}
