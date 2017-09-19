package Expression;

public class SingularMatrixException extends RuntimeException
{
	String m;
	public SingularMatrixException(String s)
	{
        m = s;
	}

	@Override
	public String getMessage()
	{
		return "Singular Matrix Exception: "+m;
	}
}


