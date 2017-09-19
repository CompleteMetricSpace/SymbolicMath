package solve;

import polynomial.GroebnerBasis;
import Expression.Expr;
import Symbolic.Constant;
import Symbolic.Int;

public class NonlinearSolve 
{
    public static Expr[][] solve_nonlinear_system(Expr[] p, Expr[] v)
    {
    	Expr[] gb = GroebnerBasis.reduced_groebner(p, v, Constant.LEXOGRAPHIC);
    	if(gb.length == 1 && gb[0].equals(Int.ONE))
    		return new Expr[][]{};
    	return null;
    }
	
}
