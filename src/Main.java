import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;

import org.apfloat.Apfloat;

import numerical.NumericalMethods;
import numerical.NumericalRational;
import calculus.Diff;
import calculus.GosperIntegrate;
import calculus.GosperSummation;
import calculus.HeuristicIntegrate;
import calculus.HeuristicLimit;
import calculus.LaplaceTransform;
import calculus.RationalIntegrate;
import calculus.RischIntegrate;
import algebra.Algebra;
import algebra.AlgebraicFunctionField;
import algebra.Denest;
import algebra.FunctionTransforms;
import algebra.LaurentSeries;
import algebra.MatchForm;
import algebra.Matrix;
import algebra.RealSeries;
import algebra.Series;
import polynomial.BasicPoly;
import polynomial.Cancel;
import polynomial.Decompose;
import polynomial.Factor;
import polynomial.FiniteField;
import polynomial.GCD;
import polynomial.GCDAlgebraicNumberField;
import polynomial.GroebnerBasis;
import polynomial.MVPoly;
import polynomial.Poly;
import polynomial.Resultant;
import polynomial.Roots;
import solve.LinearAlgebra;
import solve.Solve;
import code.*;
import Expression.Expr;
import Expression.Operator;
import Expression.Parser;
import Simplification.*;
import Symbolic.Constant;
import Symbolic.DExtension;
import Symbolic.Decimal;
import Symbolic.Greedy;
import Symbolic.Int;
import Symbolic.Mobile;
import Symbolic.ModIntSym;
import Symbolic.Num;
import Symbolic.Rational;
import Symbolic.Var;
import Symbolic.Wild;

public class Main
{
    static Var a1 = new Var("a1");
    static Var a2 = new Var("a2");
    static Var x = new Var("x");
    static Var y = new Var("y");
    static Var t = new Var("t");
    static Var z = new Var("z");
    static Var k = new Var("k");
    static Var a = new Var("a");
    static Var b = new Var("b");
    static Var w = new Var("w");

    static DExtension th_0 = new DExtension("th0", "X", x);
    static DExtension th_1 = new DExtension("th1", "EXP", th_0.pow(Int.TWO));
    static DExtension th_2 = new DExtension("th2", "LOG", th_0.add(Int.ONE));
    static DExtension[] ext = new DExtension[] {th_0, th_1, th_2};

    public static void main(String[] args) throws Exception
    {
	/*
	 * Expr n = Parser.build(
	 * "x*(x+1)*((x^2*exp(2*x^2)-log(x+1)^2)^2+2*x*exp(3*x^2)*(x-(2*x^3+2*x^2+x+1)*log(x+1)))"
	 * ); Expr d =
	 * Parser.build("((x+1)*log(x+1)^2-(x^3+x^2)*exp(2*x^2))^2");
	 * 
	 * Expr n2 = Algebra.expand(Parser.build("sqrt(11)/2*x")); Expr d2 =
	 * Algebra.expand(Parser.build("t^2+1/11"));
	 * 
	 * Expr n3 = Simplification.simplify_recursive(n2.substitute(new
	 * Expr[]{x, new Var("t1"), new Var("t2")}, new Expr[]{th_0, th_1,
	 * th_2})); Expr d3 =
	 * Simplification.simplify_recursive(d2.substitute(new Expr[]{x, new
	 * Var("t1"), new Var("t2")}, new Expr[]{th_0, th_1, th_2}));
	 * 
	 * 
	 * Expr p1 = Parser.build("-2*th0*th1^2-4*th0^3*th1^2+2*th2/(1+th0)");
	 * Expr p2 = Parser.build("-th0^2*th1^2+th2^2"); Expr p3 =
	 * Parser.build("-2*th0^3*th1^3/(1+th0)-(-2*th0^2*th1^3-4*th0^4*th1^3)*th2"
	 * );
	 * 
	 * Expr r = Parser.build("x^4+3*x^3+3*x^2-3*x+1"); Expr f =
	 * Parser.build("exp(x^2+x-3)-2"); LaurentSeries ls1 = new
	 * LaurentSeries(new Expr[]{Int.ONE, Int.TWO, Int.THREE}, new Int[]{new
	 * Int(-1), new Int(0), new Int(2)}, new Int(5)); LaurentSeries ls2 =
	 * new LaurentSeries(new Expr[]{Int.ONE, Int.FOUR}, new Int[]{new
	 * Int(-5), new Int(-2)}, new Int(5));
	 * m{{1,2,3,4,5},{1,1,1,-3,0},{0,0,1,1,4},{1,1,4,1,1}}
	 */
	Expr p1 = Parser.build("{sin(x), cos(x), x*sin(x)/(1+x^2), 1-x^2*sin(x)^2}");
	long time = System.currentTimeMillis();
	List<Expr> list = MatchForm.get_rational_independent(Arrays.asList(p1.getOperands()), x);
	
	System.out.println(list);
	
	System.out.println("timed: " + (System.currentTimeMillis() - time));
    }

    public static void test(Expr[] A)
    {
	A[0] = Int.ZERO;
    }
}
