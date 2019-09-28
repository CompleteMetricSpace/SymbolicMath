package code;

public class Statement extends Line 
{
    final String name;
    
    public static Statement BREAK = new Statement("break");
    public static Statement CONTINUE = new Statement("continue");
    
    public Statement(String n)
    {
    	name = n;
    }
    
    public boolean equals(Statement b)
    {
    	return name.equals(b.name);
    }
}
