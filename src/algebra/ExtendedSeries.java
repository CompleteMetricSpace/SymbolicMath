package algebra;

import Symbolic.Int;

/** 
 * @author KhAKhA
 *
 * Class for Extended Power Series as described in "Algorithm for Computer Algebra", GCL1992 (p.66-70)
 */
public class ExtendedSeries 
{
    private Series series;
    private Int m;
    
    public ExtendedSeries(Series s, Int m)
    {
    	series = s;
    	this.m = m;
    }
    
    public Int ord()
    {
    	return m;
    }
    
    
}
