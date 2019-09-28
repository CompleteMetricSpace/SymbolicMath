package solve;

import polynomial.Factor;
import polynomial.Poly;
import Expression.Expr;
import Expression.Operator;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Int;
import Symbolic.Rational;

public class PolySolve
{
    public static Expr[] solve_polynomial(Expr u, Expr x)
    {
        Expr[] factors = Factor.factor_poly_rationals_distinct(u);
        Expr[] S = new Expr[]{};
        for(int i = 0;i<factors.length;i++)
        	S = Set.union(S, solve_irreducible_polynomial_Q(factors[i], x));
        return S;
    }
    
	public static Expr[] solve_irreducible_polynomial_Q(Expr u, Expr x)
	{
		Int n = Poly.degree(u, x);
		if(n.equals(Int.ZERO))
			return new Expr[]{};
		if(n.equals(Int.ONE))
			return new Expr[]{Int.NONE.mul(Poly.coefficient_poly(u, x, Int.ZERO)).div(Poly.coefficient_poly(u, x, Int.ONE))};
		if(n.equals(Int.TWO))
		{
			Expr ca = Poly.coefficient_poly(u, x, Int.TWO);	
			Expr cb = Poly.coefficient_poly(u, x, Int.ONE);	
			Expr cc = Poly.coefficient_poly(u, x, Int.ZERO);
			Expr c_1 = Int.NONE.mul(cb).add(cb.mul(cb).sub(Int.FOUR.mul(ca.mul(cc))).pow(Rational.HALF)).div(Int.TWO.mul(ca));
			Expr c_2 = Int.NONE.mul(cb).sub(cb.mul(cb).sub(Int.FOUR.mul(ca.mul(cc))).pow(Rational.HALF)).div(Int.TWO.mul(ca));
            return new Expr[]{c_1, c_2};
		}
		Expr[] c = new Expr[n.toInt()];
		for(Int j = Int.ZERO;j.compareTo(n)<0;j = j.add(Int.ONE))
		{
			c[j.toInt()] = new Expr(Operator.ROOTOF, u, x, j.add(Int.ONE));
		}
		return c;
	}
	
	
}
