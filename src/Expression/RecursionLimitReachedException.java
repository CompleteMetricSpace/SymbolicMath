package Expression;

public class RecursionLimitReachedException extends Exception
{
	String m;
	int rec;
	
	public RecursionLimitReachedException(String s, int r)
	{
		m = s;
		rec = r;
	}
	
	@Override
    public String getMessage()
    {
    	return "Maximum recursion limit reached in '"+m+"': "+rec;
    }
	
	public int getLimit()
	{
		return rec;
	}
}
