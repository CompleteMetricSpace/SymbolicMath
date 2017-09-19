package calculus;

import algebra.Algebra;
import polynomial.BasicPoly;
import polynomial.Factor;
import polynomial.GCD;
import polynomial.Poly;
import polynomial.Resultant;
import solve.LinearAlgebra;
import Expression.Expr;
import Simplification.Simplification;
import Symbolic.Int;

public class GosperIntegrate 
{
    public static Expr multiple_denominator(Expr a, Expr b, Expr x)
    {
    	Expr y = Simplification.getNewVariables(1, a, b, x)[0];
    	Expr R = Resultant.multivariate_resultant(b, Algebra.expand(a.sub(y.mul(Diff.derivative(b, x)))), x, "Q");
    	Expr[] fR = Factor.factor_poly_rationals_distinct(R);
    	Int d = Int.ZERO;
    	for(int j = 0;j<fR.length;j++)
    	{
    		Expr factor = fR[j];
    		if(Poly.degree(factor, y).equals(Int.ONE))
    		{
    			Expr c_1 = Poly.coefficient_poly(factor, y, Int.ONE);
    			Expr c_0 = Poly.coefficient_poly(factor, y, Int.ZERO);
    			Expr root = c_0.mul(Int.NONE).div(c_1);
    			if(root.isInt() && ((Int)root).compareTo(d)>0)
    				d = (Int)root;
    		}
    	}
    	if(d.equals(Int.ZERO))
    		return Int.ONE;
    	Expr[] H = new Expr[d.toInt()];
    	for(int i = 0;i<H.length;i++)
    		H[i] = GCD.multivariate_gcd(b, Algebra.expand(a.sub(new Int(i+1).mul(Diff.derivative(b, x)))), "Q");
    	Expr p = Int.ONE;
    	for(int i = 0;i<H.length;i++)
    		p = Algebra.expand(p.mul(H[i].pow(new Int(i+1))));
    	return p;
    }
    
    public static Expr[] hyper_integrate(Expr a, Expr b, Expr x)
    {
    	Expr V = multiple_denominator(a, b, x);
    	Expr V_prime = Diff.derivative(V, x);
    	Expr Vb = Algebra.expand(V.mul(b));
    	Expr bVp = Algebra.expand(b.mul(V_prime).sub(a.mul(V)));
    	Expr h = GCD.multivariate_gcd(Vb, bVp, "Q");
    	Expr r = BasicPoly.polynomial_quotient(Vb, h, x);
    	Expr s = BasicPoly.polynomial_quotient(bVp, h, x);
    	Expr t = Algebra.expand(r.mul(V));
    	Int m = Int.max(Poly.degree(r, x).sub(Int.ONE), Poly.degree(s, x));
    	Expr delta = Poly.coefficient_poly(s, x, m);
    	Int e;
    	if(Poly.degree(r, x).sub(Int.ONE).compareTo(Poly.degree(s, x)) < 0 || !delta.isNaturalNumber())
    		e = Poly.degree(t, x).sub(m);
    	else
    	{
    		if(Poly.degree(t, x).sub(m).equals(delta))
    			return null;
    		else
    			e = Int.max(Poly.degree(t, x).sub(m), (Int)delta);
    	}
    	if(e.isNegative())
    		return null;
    	Expr[] cU = Simplification.getNewVariables(e.toInt()+1, a, b, x);
    	Expr U = Int.ZERO;
    	for(Int i = Int.ZERO;i.compareTo(e)<=0;i = i.add(Int.ONE))
    		U = U.add(cU[i.toInt()].mul(x.pow(i)));
    	Expr U_prime = Diff.derivative(U, x);
    	Expr eq = Algebra.expand(r.mul(U_prime).sub(s.mul(U)).sub(t));
    	int deg = Poly.degree(eq, x).toInt();
    	Expr[][] A = new Expr[deg+1][cU.length];
		Expr[] B = new Expr[deg+1];
		for(int i = 0;i<A.length;i++)
		{
			Expr coef = Poly.coefficient_poly(eq, x, new Int(i));
			for(int j = 0;j<A[i].length;j++)
			{
				A[i][j] = Poly.coefficient_poly(coef, cU[j], Int.ONE);
			}
			B[i] = Poly.coefficient_poly(coef, cU, Int.getIntList(Int.ZERO, cU.length)).mul(Int.NONE);
		}
		Expr[] X = LinearAlgebra.solve_system(A, B);
		if(X == null)
			return null;
		U = Int.ZERO;
		for(int i = 0;i<X.length;i++)
			U = U.add(X[i].mul(x.pow(new Int(i))));
		Expr gcd = GCD.multivariate_gcd(U, V, "Q");
		return new Expr[]{BasicPoly.polynomial_quotient(U, gcd, x), BasicPoly.polynomial_quotient(V, gcd, x)};
    }
    
    public static Expr[] get_a_b(Expr f, Expr x)
    {
    	Expr f_prime = Diff.derivative(f, x);
    	Expr ratio = Algebra.cancel_fractional_exponent(f_prime.div(f));
    	Expr[] nd = Algebra.NumeratorDenominator(ratio);
    	if(Poly.is_poly(nd[0], x) && Poly.is_poly(nd[1], x))
    	{
    		Expr lc = Poly.leading_coef(nd[1], x);
    		nd[1] = Algebra.expand(nd[1].div(lc));
    		nd[0] = Algebra.expand(nd[0].div(lc));
    		return nd;
    	}
    	else
    		return null;
    }
    
    public static Expr hyper_integrate(Expr a, Expr x)
    {
        Expr[] nd = get_a_b(a, x);
        if(nd == null)
        	return null;
    	Expr[] UV = hyper_integrate(nd[0], nd[1], x);
    	if(UV == null)
    		return null;
    	else
    		return Algebra.cancel(UV[0].div(UV[1]).mul(a));
    }
}
