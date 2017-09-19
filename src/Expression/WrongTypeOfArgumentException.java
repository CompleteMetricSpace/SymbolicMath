package Expression;

public class WrongTypeOfArgumentException extends RuntimeException
{
	String name;
	int args;

	public WrongTypeOfArgumentException(String s, int i)
	{
		name = s;
		args = i;
	}

	@Override
	public String getMessage()
	{
		return "Wrong type of argument in '"+name+"': "+args;
	}
}
