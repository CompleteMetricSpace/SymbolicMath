package Expression;

public class WrongNumberOfArgumentsException extends RuntimeException
{
    String name;
    int args;
    
    public WrongNumberOfArgumentsException(String s, int i)
    {
    	name = s;
    	args = i;
    }
    
    @Override
    public String getMessage()
    {
    	return "Wrong number of arguments in '"+name+"': "+args;
    }
}
