package Simplification;

import gui.InOut;

import java.util.Arrays;
import java.util.Vector;

import numerical.Evaluation;
import calculus.Diff;
import calculus.GosperIntegrate;
import calculus.GosperSummation;
import calculus.HeuristicIntegrate;
import calculus.LaplaceTransform;
import calculus.RationalIntegrate;
import calculus.RischIntegrate;
import polynomial.BasicPoly;
import polynomial.Cancel;
import polynomial.Decompose;
import polynomial.Factor;
import polynomial.GCD;
import polynomial.GroebnerBasis;
import polynomial.Poly;
import polynomial.Resultant;
import polynomial.Roots;
import algebra.Algebra;
import algebra.AlgebraicNumberField;
import algebra.Denest;
import algebra.FunctionTransforms;
import algebra.Matrix;
import algebra.Series;
import code.Programs;
import Expression.Expr;
import Expression.Operator;
import Expression.Parser;
import Expression.RecursionLimitReachedException;
import Expression.SingularMatrixException;
import Symbolic.*;

public class Simplification
{
    // Rules
    public static Rule[] simplify_rules =
    {
	    new Rule(Parser.parse("add(_x, 0)"), Parser.parse("_x"), new Var[] {new Wild("_x")}),
	    new Rule(Parser.parse("add(0, _x)"), Parser.parse("_x"), new Var[] {new Wild("_x")}),
	    new Rule(Parser.parse("multiply(_x, 1)"), Parser.parse("_x"),
		    new Var[] {new Wild("_x")}),
	    new Rule(Parser.parse("multiply(1, _x)"), Parser.parse("_x"),
		    new Var[] {new Wild("_x")}),
	    new Rule(Parser.parse("add(_x, _x)"), Parser.parse("multiply(2, _x)"),
		    new Var[] {new Wild("_x")}),
	    new Rule(Parser.parse("add(_x, multiply(_n1, _x))"),
		    Parser.parse("multiply(add(_n1, 1), _x)"), new Var[] {new Wild("_x"),
			    new Var("_n1")}),
	    new Rule(Parser.parse("add(multiply(_n2, _x), multiply(_n1, _x))"),
		    Parser.parse("multiply(add(_n2, _n1), _x)"), new Var[] {new Wild("_x"),
			    new Var("_n1"), new Var("_n2")})
    };

    private static boolean expand_constants = true, simplify_rational_int_powers = true;
    private static Operator[] no_op_simplify = {Operator.HOLD, Operator.TIME, Operator.TABLE,
	    Operator.LAZYSERIES};

    public static Expr simplify_rules(Expr expr)
    {
	for(int i = 0; i < simplify_rules.length; i++)
	{
	    Expr r = Rule.applyRule(expr, simplify_rules[i]);
	    if(!r.equals(expr))
		return simplify_rules(r);
	}
	return simplify_functions(expr);
    }

    public static boolean no_op_simplify(Operator p)
    {
	for(int i = 0; i < no_op_simplify.length; i++)
	    if(p.equals(no_op_simplify[i]))
		return true;
	return false;
    }

    public static Expr simplify_recursive(Expr expr)
    {
	if(expr.isNumerical())
	{
	    if(expr.isInt())
		return expr;
	    return ((Numerical) expr).make_normal();
	}
	if(expr instanceof Symbolic)
	    return expr;
	Expr[] args = new Expr[expr.length()];
	if(!no_op_simplify(expr.getOperator()))
	{
	    for(int i = 0; i < args.length; i++)
		args[i] = simplify_recursive(expr.get(i));
	    return simplify_functions(new Expr(expr.getOperator(), args));
	}
	return simplify_functions(expr);
    }

    public static Expr simplify_functions(Expr expr)
    {
	if(expr.getOperator().equals(Operator.ADD))
	    return simplify_sum(expr);
	if(expr.getOperator().equals(Operator.MULTIPLY))
	    return simplify_product(expr);
	if(expr.getOperator().equals(Operator.POWER))
	    return simplify_power(expr);
	if(expr.getOperator().equals(Operator.SMALLER))
	    return simplify_smaller(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.BIGGER))
	    return simplify_bigger(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.SMALLER_EQUAL))
	    return simplify_smaller_equal(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.BIGGER_EQUAL))
	    return simplify_bigger_equal(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.EQUAL))
	    return simplify_equal(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.STRUCTURE_EQUALITY))
	    return simplify_structure_equality(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.MODULUS))
	    return simplify_modulus(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.NOT))
	    return simplify_not(expr.get(0));
	if(expr.getOperator().equals(Operator.AND))
	    return simplify_and(expr);
	if(expr.getOperator().equals(Operator.OR))
	    return simplify_or(expr);
	if(expr.getOperator().equals(Operator.I_QUOTIENT))
	    return simplify_i_quotient(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.INTEGER_GCD))
	    return simplify_integer_gcd(expr.get(0));
	if(expr.getOperator().equals(Operator.INTEGER_EXTENDED_GCD))
	    return simplify_integer_extended_gcd(expr.get(0));
	if(expr.getOperator().equals(Operator.INTEGER_LCM))
	    return simplify_integer_lcm(expr.get(0));
	if(expr.getOperator().equals(Operator.EXPAND))
	    return simplify_expand(expr.getOperands());
	if(expr.getOperator().equals(Operator.RATIONALIZE))
	    return Algebra.rationalize_expand(expr.get(0));
	if(expr.getOperator().equals(Operator.CANCEL))
	    return Algebra.cancel(expr.get(0));
	if(expr.getOperator().equals(Operator.POLY_COEF))
	    return simplify_poly_coef(expr.getOperands());
	if(expr.getOperator().equals(Operator.POLY_DEGREE))
	    return simplify_poly_degree(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.POLY_REMAINDER))
	    return simplify_poly_remainder(expr.getOperands());
	if(expr.getOperator().equals(Operator.POLY_QUOTIENT))
	    return simplify_poly_quotient(expr.getOperands());
	if(expr.getOperator().equals(Operator.OPERAND))
	    return simplify_operand(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.LENGTH))
	    return simplify_length(expr.get(0));
	if(expr.getOperator().equals(Operator.KIND))
	    return simplify_kind(expr.get(0));
	if(expr.getOperator().equals(Operator.ADJOIN))
	    return simplify_adjoin(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.SET))
	    return simplify_set(expr.getOperands());
	if(expr.getOperator().equals(Operator.MEMBER))
	    return simplify_member(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.UNION))
	    return simplify_union(expr);
	if(expr.getOperator().equals(Operator.INTERSECTION))
	    return simplify_intersection(expr);
	if(expr.getOperator().equals(Operator.FORALL))
	    return simplify_forall(expr.get(0), expr.get(1), expr.get(2));
	if(expr.getOperator().equals(Operator.EXISTS))
	    return simplify_exists(expr.get(0), expr.get(1), expr.get(2));
	if(expr.getOperator().equals(Operator.FACTOR_POLYNOMIAL))
	    return simplify_factor_polynomial(expr.getOperands());
	if(expr.getOperator().equals(Operator.DECOMPOSE_POLYNOMIAL))
	    return simplify_decompose_polynomial(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.INTEGRATE_RATIONAL))
	    return simplify_integrate_rational(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.DIFFERENTIATE))
	    return simplify_differentiate(expr.getOperands());
	if(expr.getOperator().equals(Operator.RELEASE))
	    return simplify_release(expr.get(0));
	if(expr.getOperator().equals(Operator.TO_STRING))
	    return simplify_to_string(expr.get(0));
	if(expr.getOperator().equals(Operator.ADD_STRING))
	    return simplify_add_string(expr.getOperands());
	if(expr.getOperator().equals(Operator.TO_EXPR))
	    return simplify_to_expr(expr.get(0));
	if(expr.getOperator().equals(Operator.CHAR_AT))
	    return simplify_char_at(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.TIME))
	    return simplify_time(expr.get(0));
	if(expr.getOperator().equals(Operator.BIG_O))
	    return simplify_big_o(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.ABSOLUTE_VALUE))
	    return simplify_absolute_value(expr.get(0));
	if(expr.getOperator().equals(Operator.BINOMIAL))
	    return simplify_binomial(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.FACTORIAL))
	    return simplify_factorial(expr.get(0));
	if(expr.getOperator().equals(Operator.GOSPER_SUMMATION))
	    return simplify_gosper_summation(expr.getOperands());
	if(expr.getOperator().equals(Operator.SUBSTITUTE))
	    return simplify_substitute(expr.get(0), expr.get(1), expr.get(2));
	if(expr.getOperator().equals(Operator.DIFFERENCE_DELTA))
	    return simplify_difference_delta(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.GOSPER_INTEGRATION))
	    return simplify_gosper_integration(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.RISCH_INTEGRATION))
	    return simplify_risch_integration(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.EXP))
	    return SimplifyFunctions.simplify_exp(expr.get(0));
	if(expr.getOperator().equals(Operator.LOG))
	    return SimplifyFunctions.simplify_log(expr.get(0));
	if(expr.getOperator().equals(Operator.SIN))
	    return SimplifyFunctions.simplify_sin(expr.get(0));
	if(expr.getOperator().equals(Operator.COS))
	    return SimplifyFunctions.simplify_cos(expr.get(0));
	if(expr.getOperator().equals(Operator.TAN))
	    return SimplifyFunctions.simplify_tan(expr.get(0));
	if(expr.getOperator().equals(Operator.ARCSIN))
	    return SimplifyFunctions.simplify_arcsin(expr.get(0));
	if(expr.getOperator().equals(Operator.ARCCOS))
	    return SimplifyFunctions.simplify_arccos(expr.get(0));
	if(expr.getOperator().equals(Operator.ARCTAN))
	    return SimplifyFunctions.simplify_arctan(expr.get(0));
	if(expr.getOperator().equals(Operator.FDERIV))
	    return simplify_fderiv(expr.get(0), expr.get(1), expr.get(2));
	if(expr.getOperator().equals(Operator.MAXIMUM))
	    return simplify_maximum(expr.get(0));
	if(expr.getOperator().equals(Operator.GROEBNER_BASIS))
	    return simplify_groebner_basis(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.SYM_MOD_INT))
	    return simplify_sym_mod_int(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.NN_MOD_INT))
	    return simplify_nn_mod_int(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.COLLECT))
	    return simplify_collect(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.SIMPLIFY_RADICAL))
	    return simplify_simplify_radical(expr.getOperands());
	if(expr.getOperator().equals(Operator.CONTRACT))
	    return simplify_contract(expr.getOperands());
	if(expr.getOperator().equals(Operator.SIGNUM))
	    return simplify_signum(expr.get(0));
	if(expr.getOperator().equals(Operator.NUMERATOR))
	    return simplify_numerator(expr.get(0));
	if(expr.getOperator().equals(Operator.DENOMINATOR))
	    return simplify_denominator(expr.get(0));
	if(expr.getOperator().equals(Operator.PRIME_LIST))
	    return simplify_prime_list(expr.get(0));
	if(expr.getOperator().equals(Operator.POLYNOMIAL_GCD))
	    return simplify_polynomial_gcd(expr.getOperands());
	if(expr.getOperator().equals(Operator.RESULTANT))
	    return simplify_resultant(expr.get(0), expr.get(1), expr.get(2));
	if(expr.getOperator().equals(Operator.POLYNOMIAL_EXTENDED_GCD))
	    return simplify_polynomial_extended_gcd(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.SUBRESULTANT))
	    return simplify_subresultant(expr.get(0), expr.get(1), expr.get(2));
	if(expr.getOperator().equals(Operator.CYCLOTOMIC_POLYNOMIAL))
	    return simplify_cyclotomic_polynomial(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.SWINNERTON_DYER_POLYNOMIAL))
	    return simplify_swinnerton_dyer_polynomial(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.IS_PRIME))
	    return simplify_is_prime(expr.get(0));
	if(expr.getOperator().equals(Operator.FACTOR_INTEGER))
	    return simplify_factor_integer(expr.get(0));
	if(expr.getOperator().equals(Operator.INTEGRATE_HEURISTIC))
	    return simplify_integrate_heuristic(expr.get(0), expr.get(1));
	if(expr.getOperator().equals(Operator.SIMPLIFY_SIDE_RELATIONS))
	    return simplify_simplify_side_relations(expr.get(0), expr.get(1), expr.get(2));
	if(expr.getOperator().equals(Operator.NUMERICAL_EVAL))
	    return simplify_numerical_eval(expr.getOperands());
	if(expr.getOperator().equals(Operator.INTEGER_CHINESE_REMAINDER))
	    return simplify_integer_chinese_remainder(expr.get(0));
	if(expr.getOperator().equals(Operator.DENEST))
	    return simplify_denest(expr.get(0));
	if(expr.getOperator().equals(Operator.ISOLATE_ROOTS))
	    return simplify_isolate_roots(expr.getOperands());
	if(expr.getOperator().equals(Operator.TABLE))
	    return simplify_table(expr.getOperands());
	if(expr.getOperator().equals(Operator.MATRIX))
	    return simplify_matrix(expr.get(0));
	if(expr.getOperator().equals(Operator.DETERMINANT))
	    return simplify_determinant(expr.get(0));
	if(expr.getOperator().equals(Operator.REDUCED_ROW_ECHELON))
	    return simplify_reduced_row_echelon(expr.get(0));
	if(expr.getOperator().equals(Operator.TRANSPOSE))
	    return simplify_transpose(expr.get(0));
	if(expr.getOperator().equals(Operator.COFACTOR_MATRIX))
	    return simplify_cofactor_matrix(expr.get(0));
	if(expr.getOperator().equals(Operator.IDENTITY_MATRIX))
	    return simplify_identity_matrix(expr.get(0));
	if(expr.getOperator().equals(Operator.LAPLACE_TRANSFORM))
	    return simplify_laplace_transform(expr.get(0), expr.get(1), expr.get(2));
	// Simplify Programs:
	Operator op = expr.getOperator();
	for(int i = 0; i < Programs.prgms.length; i++)
	{
	    if(Programs.prgms[i].getName().equals(op.getName())
		    && Programs.prgms[i].getParameters().length == expr.length())
	    {
		try
		{
		    Expr p = Programs.prgms[i].execute(expr.getOperands()).getReturnExpr();
		    if(p == null)
			return Constant.VOID;
		    return p;
		}
		catch(Exception e)
		{
		    e.printStackTrace();
		}
	    }
	}
	if(expr.getOperator().isCommutative())
	    expr = simplify_commutative(expr.getOperands(), expr.getOperator());
	return expr;
    }

    private static Expr simplify_laplace_transform(Expr a, Expr b, Expr c)
    {
	try
	{
	    Expr h = LaplaceTransform.laplace_transform(a, b, c);
	    if(h.equals(Constant.FAIL))
	    {
		InOut.parser_output("[LaplaceTransform] Warning: Failed to find the laplace transform");
		return Constant.FAIL;
	    }
	    return h;
	}
	catch(RecursionLimitReachedException e)
	{
	    InOut.parser_output("[LaplaceTransform] Maximum recursion limit reached: "
		    + e.getLimit());
	    return Constant.FAIL;
	}
    }

    private static Expr simplify_identity_matrix(Expr n)
    {
	if(n.isNumerical())
	{
	    if(n.isInt())
	    {
		Int N = (Int) n;
		if(N.compareTo(new Int(Integer.MAX_VALUE)) > 0)
		    throw new IllegalArgumentException(N + " is too big for this implementation");
		if(N.isPositive())
		    return new Expr(Operator.MATRIX, Set.toList(Matrix.identity_matrix(N.toInt())));
	    }
	    throw new IllegalArgumentException(n + " is not a positive integer");
	}
	return new Expr(Operator.IDENTITY_MATRIX, n);
    }

    private static Expr simplify_cofactor_matrix(Expr a)
    {
	if(a.isMatrix())
	{
	    return new Expr(Operator.MATRIX, Set.toList(Matrix.cofactor_matrix(Set.toExprArray(a
		    .get(0)))));
	}
	return new Expr(Operator.TRANSPOSE, a);
    }

    private static Expr simplify_transpose(Expr a)
    {
	if(a.isMatrix())
	{
	    return new Expr(Operator.MATRIX,
		    Set.toList(Matrix.transpose(Set.toExprArray(a.get(0)))));
	}
	return new Expr(Operator.TRANSPOSE, a);
    }

    private static Expr simplify_reduced_row_echelon(Expr a)
    {
	if(a.isMatrix())
	{
	    Expr[][] M = Set.toExprArray(a.get(0));
	    Expr[][] C = Matrix.row_echelon(M, M.length, true);
	    return new Expr(Operator.MATRIX, Set.toList(C));
	}
	return new Expr(Operator.REDUCED_ROW_ECHELON, a);
    }

    private static Expr simplify_determinant(Expr a)
    {
	if(a.isMatrix())
	{
	    return Matrix.determinant(Set.toExprArray(a.get(0)));
	}
	return new Expr(Operator.DETERMINANT, a);
    }

    private static Expr simplify_matrix(Expr a)
    {
	if(a.isList() && a.length() > 0)
	{
	    int n = a.length();
	    int s = 0;
	    for(int i = 0; i < n; i++)
	    {
		if(!(a.get(i).isList()))
		    throw new IllegalArgumentException(a + " is not a matrix");
		else
		{
		    if(i == 0)
		    {
			s = a.get(i).length();
			if(s == 0)
			    throw new IllegalArgumentException(a + " is not a matrix");
		    }
		    else
		    {
			if(s != a.get(i).length())
			    throw new IllegalArgumentException(a + " is not a matrix");
		    }
		}
	    }
	    return new Expr(Operator.MATRIX, a);
	}
	throw new IllegalArgumentException(a + " is not a matrix");
    }

    private static Expr simplify_table(Expr[] p)
    {
	Expr a = p[0], b = p[1], c = simplify_recursive(p[2]), d = simplify_recursive(p[3]);
	if(c.isInt() && d.isInt())
	{
	    Int C = (Int) c, D = (Int) d;
	    if(C.compareTo(D) > 0)
		throw new IllegalArgumentException(C + " is bigger than " + D);
	    Int F = D.sub(C).add(Int.ONE);
	    if(F.compareTo(new Int(Integer.MAX_VALUE)) > 0)
		throw new IllegalArgumentException("difference between " + C + " and " + D
			+ " is too big");
	    Expr[] list = new Expr[F.toInt()];
	    int i = 0;
	    for(Int j = C; j.compareTo(D) <= 0; j = j.add(Int.ONE))
	    {
		list[i] = simplify_recursive(a.substitute(b, j));
		i = i + 1;
	    }
	    return new Expr(Operator.LIST, list);
	}
	return new Expr(Operator.TABLE, p);
    }

    private static Expr simplify_isolate_roots(Expr[] a)
    {
	Expr u = a[0];
	Expr x = a[1];
	if(!Poly.is_poly_Q(u, x))
	    throw new IllegalArgumentException(u + " is not a polynomial in Q[" + x + "]");
	// Make square free
	Expr gcd = GCD.multivariate_gcd(u, Diff.derivative(u, x), "Q");
	u = BasicPoly.polynomial_quotient(u, gcd, x);
	if(a.length == 2)
	{
	    Numerical[][] s = Roots.isolate_roots(u, x);
	    return Set.toList(s);
	}
	if(a.length == 3 && a[2].isNumerical())
	{
	    Numerical[][] s = Roots.isolate_roots(u, x, (Numerical) a[2]);
	    return Set.toList(s);
	}
	return new Expr(Operator.ISOLATE_ROOTS, a);
    }

    private static Expr simplify_denest(Expr a)
    {
	return Denest.simplify_nested_sqrt_op(a);
    }

    private static Expr simplify_integer_chinese_remainder(Expr e)
    {
	if(e.isList())
	{
	    Expr[] x = e.getOperands();
	    if(x.length == 0)
		throw new IllegalArgumentException(e + " is empty");
	    Int[] M = new Int[x.length];
	    Int[] X = new Int[x.length];
	    for(int i = 0; i < x.length; i++)
	    {
		if(x[i].isList() && x[i].length() == 2 && x[i].get(0).isInt()
			&& x[i].get(1).isInt())
		{
		    Int a = (Int) x[i].get(0);
		    Int b = (Int) x[i].get(1);
		    M[i] = b;
		    if(!b.isNaturalNumber())
			throw new IllegalArgumentException("modulus " + b
				+ " is not a positive integer");
		    X[i] = a.mod(b);
		}
		else
		    throw new IllegalArgumentException(x[i] + " is not a list of two integers");
	    }
	    if(!Int.pairwise_relatively_prime(M))
		throw new IllegalArgumentException("moduli are not pairwise relatively prime");
	    return Int.integer_chinese_remainder(M, X);
	}
	throw new IllegalArgumentException(e + " is not a list");
    }

    private static Expr simplify_numerical_eval(Expr[] a)
    {
	if(a.length == 2)
	{
	    if(a[1].isInt() && is_positive(a[1]))
		return Evaluation.evaluate(a[0], ((Int) a[1]).toInt());
	}
	else
	{
	    return Evaluation.evaluate(a[0], Decimal.DEFAULT_PRECISION);
	}
	return new Expr(Operator.NUMERICAL_EVAL, a);
    }

    private static Expr simplify_simplify_side_relations(Expr a, Expr b, Expr c)
    {
	Expr[] vl = c.isList() ? c.getOperands() : new Expr[] {c};
	Expr[] sr = b.isList() ? b.getOperands() : new Expr[] {b};
	a = Algebra.expand(a);
	if(!Poly.is_poly(a, vl))
	    throw new IllegalArgumentException(a + " is not a multivariate polynomial in Q"
		    + Expr.toString(vl));
	for(int i = 0; i < sr.length; i++)
	    if(!Poly.is_poly(sr[i], vl))
		throw new IllegalArgumentException(sr[i] + " is not a multivariate polynomial in Q"
			+ Expr.toString(vl));
	Expr s = GroebnerBasis.simplify_poly(a, sr, vl);
	if(s == null)
	{
	    InOut.parser_output("[GroebnerBasis] Inconsistent side relations");
	    return Constant.FAIL;
	}
	return s;
    }

    private static Expr simplify_integrate_heuristic(Expr u, Expr x)
    {
	try
	{
	    Expr h = HeuristicIntegrate.integrate(u, x);
	    if(h.equals(Constant.FAIL))
	    {
		InOut.parser_output("[HeuristicIntegrate] Warning: No antiderivative found");
		return Constant.FAIL;
	    }
	    return h;
	}
	catch(RecursionLimitReachedException e)
	{
	    InOut.parser_output("[HeuristicIntegrate] Maximum recursion limit reached: "
		    + e.getLimit());
	    return Constant.FAIL;
	}
    }

    private static Expr simplify_factor_integer(Expr n)
    {
	if(n.isInt())
	{
	    boolean neg = false;
	    Int N = (Int) n;
	    if(N.isNegative())
	    {
		neg = true;
		N = N.abs();
	    }
	    if(N.equals(Int.ZERO))
		return new Expr(Operator.LIST, Int.ZERO);
	    Int[][] f = N.factor();
	    Expr[] e = new Expr[f.length];
	    for(int i = 0; i < e.length; i++)
		e[i] = new Expr(Operator.LIST, f[i]);
	    if(neg)
		e = Set.add(new Expr[] {new Expr(Operator.LIST, Int.NONE, Int.ONE)}, e);
	    return new Expr(Operator.LIST, e);
	}
	return new Expr(Operator.FACTOR_INTEGER, n);
    }

    private static Expr simplify_is_prime(Expr n)
    {
	if(n.isInt())
	{
	    if(n.equals(Int.ZERO))
		return Constant.FALSE;
	    if(((Int) n).abs().isPrime())
		return Constant.TRUE;
	    return Constant.FALSE;
	}
	return new Expr(Operator.IS_PRIME, n);
    }

    private static Expr simplify_swinnerton_dyer_polynomial(Expr x, Expr n)
    {
	if(n.isInt())
	{
	    Int N = (Int) n;
	    if(N.compareTo(new Int("15")) > 0)
		throw new IllegalArgumentException(N + " is too big for this implementation");
	    if(N.compareTo(Int.ZERO) <= 0)
		throw new IllegalArgumentException(N + " is not a positive integer");
	    return BasicPoly.swinnerton_dyer_polynomial(x, N);
	}
	return new Expr(Operator.SWINNERTON_DYER_POLYNOMIAL, x, n);
    }

    private static Expr simplify_cyclotomic_polynomial(Expr x, Expr n)
    {
	if(n.isInt())
	{
	    Int N = (Int) n;
	    if(N.compareTo(new Int("10000")) > 0)
		throw new IllegalArgumentException(N + " is too big for this implementation");
	    if(N.compareTo(Int.ZERO) <= 0)
		throw new IllegalArgumentException(N + " is not a positive integer");
	    return BasicPoly.cyclotomic_polynomial(x, N);
	}
	return new Expr(Operator.CYCLOTOMIC_POLYNOMIAL, x, n);
    }

    private static Expr simplify_subresultant(Expr u, Expr v, Expr x)
    {
	if(Poly.is_poly(u, x) && Poly.is_poly(v, x))
	{
	    Expr[] res = Resultant.multivariate_subresultant(u, v, x, "Q");
	    return new Expr(Operator.LIST, res);
	}
	else
	    throw new IllegalArgumentException(u + " or " + v + " is/are not polynomials in " + x);
    }

    private static Expr simplify_polynomial_extended_gcd(Expr list, Expr x)
    {
	if(list.isList())
	{
	    Expr[] l = list.getOperands();
	    if(Poly.are_poly(l, new Expr[] {x}))
	    {
		Expr[] gcd = GCD.polynomial_extended_gcd(l, x);
		Expr U = gcd[0];
		Expr[] r = Set.rest(gcd);
		return new Expr(Operator.LIST, U, new Expr(Operator.LIST, r));
	    }
	    else
		throw new IllegalArgumentException("<pextgcd>: " + list
			+ " are not polynomials in " + x);
	}
	return new Expr(Operator.POLYNOMIAL_EXTENDED_GCD, list, x);
    }

    private static Expr simplify_resultant(Expr u, Expr v, Expr x)
    {
	u = Algebra.expand(u);
	v = Algebra.expand(v);
	if(Poly.is_poly(u, x) && Poly.is_poly(v, x))
	{
	    return Resultant.multivariate_resultant(u, v, x, "Q");
	}
	else
	    throw new IllegalArgumentException("<resultant>: " + u + " or " + v
		    + " is/are not polynomials in " + x);
    }

    private static Expr simplify_polynomial_gcd(Expr... list)
    {
	if(list.length == 1 && list[0].isList())
	{
	    Expr[] ps = list[0].getOperands();
	    return GCD.multivariate_gcd(ps, "Q");
	}
	if(list.length == 2)
	{
	    if(list[0].isList() && list[1].getOperator().equals(Operator.MODULO))
	    {
		Int m = (Int) list[1].get(0);
		if(!m.isPrime())
		    throw new IllegalArgumentException(m + " is not a prime number");
		Expr[] ps = list[0].getOperands();
		Expr[] vars = new Expr[] {};
		for(int i = 0; i < ps.length; i++)
		{
		    Expr[] vars_i = Poly.variables(ps[i]);
		    if(!Poly.is_poly_Z(ps[i], vars_i))
			throw new IllegalArgumentException(ps[i]
				+ " is not a polynomial with coefficients in Z_" + m);
		    vars = Set.union(vars, vars_i);
		}
		return GCD.modular_gcd_p(ps, vars, m);
	    }
	    if(list[0].isList() && list[1].getOperator().equals(Operator.ALGEBRAIC_EXTENSION))
	    {
		Expr a = list[1].get(0);
		Expr p = list[1].get(1);
		Expr[] ps = list[0].getOperands();
		Expr[] vars = new Expr[] {};
		for(int i = 0; i < ps.length; i++)
		    vars = Set.union(vars, Poly.variables(ps[i]));
		vars = Set.complement(vars, new Expr[] {a});
		return GCD.multivariate_gcd_anf(ps, vars, new Expr[] {p}, new Expr[] {a});
	    }
	}
	return new Expr(Operator.POLYNOMIAL_GCD, list);
    }

    private static Expr simplify_prime_list(Expr n)
    {
	if(n.isNumerical())
	{
	    if(!n.isInt())
		throw new IllegalArgumentException(n + " is not an integer");
	    Int N = (Int) n;
	    if(N.compareTo(Int.TWO) < 0)
		return new Expr(Operator.LIST);
	    if(N.equals(Int.TWO))
		return new Expr(Operator.LIST, Int.TWO);
	    if(N.compareTo(new Int("300000")) > 0)
		throw new IllegalArgumentException(n + " is too big for this implementation");
	    Int[] l = Int.sieve_odd(N.toInt());
	    return new Expr(Operator.LIST, Set.add(new Expr[] {Int.TWO}, l));
	}
	if(n instanceof Constant)
	    throw new IllegalArgumentException(n + " is not an integer");
	return new Expr(Operator.PRIME_LIST, n);
    }

    private static Expr simplify_denominator(Expr a)
    {
	return Algebra.NumeratorDenominator(a)[1];
    }

    private static Expr simplify_numerator(Expr a)
    {
	return Algebra.NumeratorDenominator(a)[0];
    }

    private static Expr simplify_signum(Expr a)
    {
	if(a.equals(Int.ZERO))
	    return Int.ZERO;
	Numerical[] gr = gaussian_rational(a);
	if(gr != null)
	{
	    Expr abs = gr[0].pow(Int.TWO).add(gr[1].pow(Int.TWO)).pow(Rational.HALF);
	    return Algebra.expand(a.div(abs));
	}
	if(a.isProduct())
	{
	    Expr[] s = new Expr[a.length()];
	    for(int i = 0; i < s.length; i++)
		s[i] = simplify_signum(a.get(i));
	    return simplify_product(new Expr(Operator.MULTIPLY, s));
	}
	if(a.isPower())
	{
	    Expr b = a.get(0);
	    Expr e = a.get(1);
	    if(e.isInt())
		return simplify_integer_pow(simplify_signum(b), (Int) e);
	}
	return new Expr(Operator.SIGNUM, a);
    }

    private static Expr simplify_contract(Expr[] op)
    {
	if(op.length == 1)
	    return FunctionTransforms.contract_all(op[0]);
	Expr a = op[0];
	Expr b = op[1];
	Expr[] list = b.isList() ? b.getOperands() : new Expr[] {b};
	for(int i = 0; i < list.length; i++)
	{
	    if(list[i].equals(new Str("exp")))
		a = FunctionTransforms.contract_exp(a);
	    if(list[i].equals(new Str("log")))
		a = FunctionTransforms.contract_log(a);
	    if(list[i].equals(new Str("trig")))
		a = FunctionTransforms.contract_trig(a);
	}
	return a;
    }

    private static Expr simplify_simplify_radical(Expr[] a)
    {
	if(a.length == 1)
	    return AlgebraicNumberField.simplify_in_A(a[0], Constant.VOID);
	else
	    return AlgebraicNumberField.simplify_in_A(a[0], a[1]);
    }

    private static Expr simplify_collect(Expr a, Expr b)
    {
	Expr[] c = b.isList() ? b.getOperands() : new Expr[] {b};
	return Algebra.collect(a, c);
    }

    private static Expr simplify_nn_mod_int(Expr a, Expr b)
    {
	if(a.isInt() && b.isInt())
	    return new ModIntNon((Int) a, (Int) b);
	return new Expr(Operator.NN_MOD_INT, a, b);
    }

    private static Expr simplify_sym_mod_int(Expr a, Expr b)
    {
	if(a.isInt() && b.isInt())
	    return new ModIntSym((Int) a, (Int) b);
	return new Expr(Operator.SYM_MOD_INT, a, b);
    }

    private static Expr simplify_groebner_basis(Expr a, Expr b)
    {
	if(a.isList() && b.isList())
	{
	    Expr[] A = a.getOperands();
	    Expr[] B = b.getOperands();
	    if(!Poly.are_poly(A, B))
		throw new IllegalArgumentException(a + " is not a list of polynomials in " + b);
	    Expr[] R = GroebnerBasis.reduced_groebner(A, B, GroebnerBasis.DEFAULT_ORDER);
	    return new Expr(Operator.LIST, R);
	}
	return new Expr(Operator.GROEBNER_BASIS, a, b);
    }

    private static Expr simplify_maximum(Expr list)
    {
	if(list.isList())
	{
	    Expr[] l = list.getOperands();
	    Vector<Expr> big_list = new Vector<Expr>();
	    for(int i = 0; i < l.length; i++)
	    {
		Expr v = l[i];
		if(v.getOperator().equals(Operator.MAXIMUM))
		{
		    Expr m = v.get(0);
		    if(m.isList())
		    {
			for(int j = 0; j < m.length(); j++)
			    big_list.add(m.get(j));
		    }
		    else
			big_list.add(v);
		}
		else
		    big_list.add(v);
	    }
	    Expr[] M = big_list.toArray(new Expr[big_list.size()]);
	    Expr[] max = Algebra.max(M);
	    if(max.length == 1)
		return max[0];
	    max = merge_sort(max);
	    return new Expr(Operator.MAXIMUM, new Expr(Operator.LIST, max));
	}
	return new Expr(Operator.MAXIMUM, list);
    }

    private static Expr simplify_fderiv(Expr f, Expr n, Expr v)
    {
	if(f.isVar() && !(f instanceof Operator))
	{
	    String s = ((Var) f).getName();
	    int ops = v.isList() ? v.length() : 1;
	    return simplify_fderiv(new Operator(s, s, "function", false, ops), n, v);
	}
	if(n.isList() && n.length() == 1 && v.isList() && v.length() == 1)
	    return simplify_fderiv(f, n.get(0), v.get(0));
	if(n.equals(Int.ZERO))
	{
	    return new Expr((Operator) f, v);
	}
	if(n.isList())
	{
	    boolean not_zero = false;
	    for(int i = 0; i < n.length(); i++)
		if(!n.get(i).equals(Int.ZERO))
		    not_zero = true;
	    if(!not_zero)
		return new Expr((Operator) f, v);
	}
	return new Expr(Operator.FDERIV, f, n, v);
    }

    private static Expr simplify_risch_integration(Expr f, Expr x)
    {
	f = RischIntegrate.normal(f, x);
	if(!RischIntegrate.is_exp_log_function(f, x))
	    throw new IllegalArgumentException(f
		    + " is not a pure transcendental exp-log-elementary function");
	Expr ri = RischIntegrate.integrate_risch(f, x);
	if(ri == null)
	{
	    InOut.parser_output("[RischIntegrate] Warning: No elementary antiderivative found");
	    return Constant.FAIL;
	}
	return Algebra.cancel(ri);
    }

    private static Expr simplify_gosper_integration(Expr f, Expr x)
    {
	Expr[] ab = GosperIntegrate.get_a_b(f, x);
	if(ab == null)
	    throw new IllegalArgumentException(f
		    + " is apparently not a hypergeometric term over Q(" + x + ")");
	Expr[] hi = GosperIntegrate.hyper_integrate(ab[0], ab[1], x);
	if(hi == null)
	{
	    InOut.parser_output("[GosperIntegrate] Warning: No hypergeometric antiderivative found");
	    return Constant.FAIL;
	}
	return Algebra.cancel(hi[0].div(hi[1]).mul(f));
    }

    private static Expr simplify_difference_delta(Expr a, Expr k)
    {
	return a.substitute(k, k.add(Int.ONE)).sub(a);
    }

    private static Expr simplify_substitute(Expr a, Expr b, Expr c)
    {
	return simplify_recursive(a.substitute(b, c));
    }

    private static Expr simplify_gosper_summation(Expr[] p)
    {
	Expr a = p[0];
	Expr k = p[1];
	Expr[] uv = GosperSummation.get_u_v(a, k);
	if(uv == null)
	    throw new IllegalArgumentException(a
		    + " is apparently not a hypergeometric term over Q(" + k + ")");
	Expr gs = GosperSummation.gosper(a, uv[0], uv[1], k);
	if(gs == null)
	{
	    InOut.parser_output("[GosperSummation] Warning: No hypergeometric antidifference found");
	    return Constant.FAIL;
	}
	if(p.length == 2)
	    return gs;
	else
	    return gs.substitute(k, p[3].add(Int.ONE)).sub(gs.substitute(k, p[2]));
    }

    private static Expr simplify_factorial(Expr a)
    {
	if(a.isInt())
	{
	    Int A = (Int) a;
	    if(A.isPositive() || A.equals(Int.ZERO))
		return A.factorial();
	    else
		return Constant.UNDEFINED;
	}
	return new Expr(Operator.FACTORIAL, a);
    }

    private static Expr simplify_binomial(Expr a, Expr b)
    {
	if(a.equals(Int.ZERO))
	    return Int.ZERO;
	if(b.equals(Int.ZERO))
	    return Int.ONE;
	if(a.isInt() && b.isInt())
	{
	    Int A = (Int) a;
	    Int B = (Int) b;
	    return Int.binom(A, B);
	}
	return new Expr(Operator.BINOMIAL, a, b);
    }

    private static Expr simplify_absolute_value(Expr a)
    {
	if(a.equals(Constant.I))
	    return Int.ONE;
	Numerical[] gr = gaussian_rational(a);
	if(gr != null)
	{
	    if(gr[1].equals(Int.ZERO))
		return gr[0].abs();
	    if(gr[0].equals(Int.ZERO))
		return gr[1].abs();
	    return gr[0].pow(Int.TWO).add(gr[1].pow(Int.TWO)).pow(Rational.HALF);
	}
	if(a.isProduct())
	{
	    Expr[] s = new Expr[a.length()];
	    for(int i = 0; i < s.length; i++)
		s[i] = simplify_absolute_value(a.get(i));
	    return simplify_product(new Expr(Operator.MULTIPLY, s));
	}
	if(a.isPower())
	{
	    Expr b = a.get(0);
	    Expr e = a.get(1);
	    if(e.isInt())
		return simplify_integer_pow(simplify_absolute_value(b), (Int) e);
	}
	return new Expr(Operator.ABSOLUTE_VALUE, a);
    }

    private static Expr simplify_time(Expr a)
    {
	long time = System.currentTimeMillis();
	Expr c = simplify_recursive(a);
	time = System.currentTimeMillis() - time;
	return new Expr(Operator.LIST, new Int((int) time), c);
    }

    private static Expr simplify_char_at(Expr p, Expr n)
    {
	if(p instanceof Str && n.isInt())
	{
	    String s = ((Str) p).getString();
	    int j = ((Int) n).toInt();
	    if(j >= 0 && j < s.length())
		return new Str("" + s.charAt(j));
	    return new Str("");
	}
	return new Expr(Operator.CHAR_AT, p, n);
    }

    private static Expr simplify_to_expr(Expr p)
    {
	if(p instanceof Str)
	{
	    Expr parse = Parser.parse(((Str) p).getString());
	    return Simplification.simplify_recursive(parse);
	}
	return new Expr(Operator.TO_EXPR, p);
    }

    private static Expr simplify_add_string(Expr[] p)
    {
	Expr[] l;
	if(p.length == 1 && p[0].isList())
	    l = p[0].getOperands();
	else
	    l = p;
	String s = "";
	for(int i = 0; i < l.length; i++)
	{
	    if(!(l[i] instanceof Str))
		return new Expr(Operator.ADD_STRING, p);
	    s = s + ((Str) l[i]).getString();
	}
	return new Str(s);
    }

    private static Expr simplify_big_o(Expr a, Expr n)
    {
	if(a.getOperator().equals(Operator.BIG_O) && a.get(1).equals(n))
	    return simplify_big_o(a.get(0), n);
	Expr[] cv = constant_term(a, n);
	if(!cv[0].equals(Int.ONE))
	    return simplify_big_o(cv[1], n);
	return new Expr(Operator.BIG_O, a, n);
    }

    private static Expr simplify_to_string(Expr a)
    {
	return new Str(a.toString2());
    }

    private static Expr simplify_release(Expr a)
    {
	if(a.getOperator().equals(Operator.NULL))
	    return a;
	Expr[] args = new Expr[a.length()];
	for(int i = 0; i < args.length; i++)
	    args[i] = simplify_release(a.get(i));
	if(a.getOperator().equals(Operator.HOLD))
	    return simplify_recursive(args[0]);
	else
	    return simplify_recursive(new Expr(a.getOperator(), args));
    }

    private static Expr simplify_differentiate(Expr[] a)
    {
	if(a.length == 1)
	    return Diff.derivative(a[0], Constant.VOID);
	return Diff.derivative(a[0], a[1]);
    }

    private static Expr simplify_integrate_rational(Expr a, Expr b)
    {
	Expr c = Algebra.cancel(a);
	Expr[] nd = Algebra.NumeratorDenominator(c);
	Expr n = nd[0], d = nd[1];
	Expr[] v = Set.union(Poly.variables(n), Poly.variables(d));
	if(v.length == 0 || v.length == 1 && v[0].equals(b))
	{
	    return RationalIntegrate.integrate_rational_function(n, d, b);
	}
	return new Expr(Operator.INTEGRATE_RATIONAL, a, b);
    }

    private static Expr simplify_decompose_polynomial(Expr u, Expr x)
    {
	Expr[] vars = Poly.variables(u);
	if(vars.length == 1 && vars[0].equals(x))
	{
	    return new Expr(Operator.LIST, Decompose.decompose_fast(u, x));
	}
	return new Expr(Operator.LIST, u);
    }

    private static Expr simplify_factor_polynomial(Expr[] p)
    {
	if(p.length == 1)
	{
	    return Factor.factor_poly_rationals_expr(p[0]);
	}
	else
	{
	    Expr u = p[0];
	    Expr option = p[1];
	    if(option.getOperator().equals(Operator.MODULO))
	    {
		Expr P = option.get(0);
		if(P.isInt())
		{
		    Int m = (Int) P;
		    if(!m.isPrime())
			throw new IllegalArgumentException(m + " is not a prime number");
		    Expr[] vars = Poly.variables(u);
		    if(vars.length > 1)
			throw new IllegalArgumentException(
				"Cannot factor a multivariate polynomial over a finite field");
		    if(!Poly.is_poly_Z(u, vars))
			throw new IllegalArgumentException(u
				+ " is not a polynomial with coefficients in Z_" + m);
		    if(vars.length == 0)
			return u;
		    Expr x = getNewVariables(1, u)[0];
		    u = simplify_recursive(u.substitute(vars[0], x));
		    Expr factor = Factor.factor_poly_p_expr(u, x, m);
		    return simplify_recursive(factor.substitute(x, vars[0]));
		}
	    }
	    if(option.getOperator().equals(Operator.ALGEBRAIC_EXTENSION))
	    {
		Expr m = option.get(1);
		Expr alpha = option.get(0);
		if(m.isList())
		    throw new IllegalArgumentException(
			    "Cannot factor over a non-simple algebraic extension");
		Expr[] vars = Set.complement(Poly.variables(u), new Expr[] {alpha});
		if(vars.length == 0)
		    return u;
		if(vars.length > 1)
		    throw new IllegalArgumentException(
			    "Cannot factor a multivariate polynomial over an algebraic number field");
		Expr x = vars[0];
		if(!Poly.is_poly_Q(m, alpha))
		    throw new IllegalArgumentException(m + " is not a polynomial in Q[" + alpha
			    + "]");
		Expr f = Factor.factor_poly_algebraic_number_field_expr(u, x, m, alpha);
		return f;
	    }
	}
	return new Expr(Operator.FACTOR_POLYNOMIAL, p);
    }

    private static Expr simplify_exists(Expr a, Expr b, Expr c)
    {
	if(c.isFreeOf(a))
	    return c;
	if(b.getOperator().equals(Operator.SET))
	{
	    if(b.length() == 1)
	    {
		Expr list = b.get(0);
		Expr[] es = new Expr[list.length()];
		for(int i = 0; i < es.length; i++)
		{
		    es[i] = simplify_recursive(c.substitute(a, list.get(i)));
		    if(es[i].equals(Constant.TRUE))
			return Constant.TRUE;
		}
		return simplify_or(new Expr(Operator.OR, es));
	    }
	}
	return new Expr(Operator.EXISTS, a, b, c);
    }

    private static Expr simplify_forall(Expr a, Expr b, Expr c)
    {
	if(c.isFreeOf(a))
	    return c;
	if(b.getOperator().equals(Operator.SET))
	{
	    if(b.length() == 1)
	    {
		Expr list = b.get(0);
		Expr[] es = new Expr[list.length()];
		for(int i = 0; i < es.length; i++)
		{
		    es[i] = simplify_recursive(c.substitute(a, list.get(i)));
		    if(es[i].equals(Constant.FALSE))
			return Constant.FALSE;
		}
		return simplify_and(new Expr(Operator.AND, es));
	    }
	}
	return new Expr(Operator.FORALL, a, b, c);
    }

    private static Expr simplify_bigger_equal(Expr a, Expr b)
    {
	if(a.isNumerical() && b.isNumerical())
	{
	    int h = ((Numerical) a).compareTo((Numerical) b);
	    if(h == 1 || h == 0)
		return Constant.TRUE;
	    else
		return Constant.FALSE;
	}
	return new Expr(Operator.BIGGER_EQUAL, a, b);
    }

    private static Expr simplify_smaller_equal(Expr a, Expr b)
    {
	if(a.isNumerical() && b.isNumerical())
	{
	    int h = ((Numerical) a).compareTo((Numerical) b);
	    if(h == -1 || h == 0)
		return Constant.TRUE;
	    else
		return Constant.FALSE;
	}
	return new Expr(Operator.SMALLER_EQUAL, a, b);
    }

    private static Expr simplify_bigger(Expr a, Expr b)
    {
	if(a.isNumerical() && b.isNumerical())
	{
	    int h = ((Numerical) a).compareTo((Numerical) b);
	    if(h == 1)
		return Constant.TRUE;
	    else
		return Constant.FALSE;
	}
	return new Expr(Operator.BIGGER, a, b);
    }

    private static Expr simplify_member(Expr a, Expr b)
    {
	if(b.getOperator().equals(Operator.SET))
	{
	    if(b.length() == 1)
	    {
		boolean w = Set.member(b.get(0).getOperands(), a);
		if(w)
		    return Constant.TRUE;
		else
		    return Constant.FALSE;
	    }
	    else
	    {
		Expr A = b.get(1);
		Expr x = b.get(0);
		Expr f = simplify_recursive(A.substitute(x, a));
		return f;
	    }
	}
	return new Expr(Operator.MEMBER, a, b);
    }

    private static Expr simplify_set(Expr[] L)
    {
	if(L.length == 2)
	    return new Expr(Operator.SET, L);
	Expr list = L[0];
	Expr[] n = new Expr[list.length()];
	for(int i = 0; i < n.length; i++)
	    n[i] = list.get(i);
	n = Set.remove_dublicates(n);
	return new Expr(Operator.SET, new Expr(Operator.LIST, merge_sort(n)));
    }

    private static Expr simplify_expand(Expr[] op)
    {
	if(op.length == 1)
	    return Algebra.expand(op[0]);
	Expr a = op[0];
	Expr b = op[1];
	Expr[] list = b.isList() ? b.getOperands() : new Expr[] {b};
	for(int i = 0; i < list.length; i++)
	{
	    if(list[i].equals(new Str("exp")))
		a = FunctionTransforms.expand_exp(a);
	    if(list[i].equals(new Str("log")))
		a = FunctionTransforms.expand_log(a);
	    if(list[i].equals(new Str("trig")))
		a = FunctionTransforms.expand_trig(a);
	    if(list[i].equals(new Str("alg")))
		a = Algebra.expand(a);
	    if(list[i].equals(new Str("all")))
		a = Algebra.expand(FunctionTransforms.expand_all(a));
	    if(list[i].equals(new Str("full")))
		a = Algebra.expand_full(a);
	}
	return a;
    }

    private static Expr simplify_integer_lcm(Expr list)
    {
	if(list.isList())
	{
	    Expr[] l = list.getOperands();
	    Vector<Expr> big_list = new Vector<Expr>();
	    for(int i = 0; i < l.length; i++)
	    {
		Expr v = l[i];
		if(v.getOperator().equals(Operator.INTEGER_LCM))
		{
		    Expr m = v.get(0);
		    if(m.isList())
		    {
			for(int j = 0; j < m.length(); j++)
			    big_list.add(m.get(j));
		    }
		    else
			big_list.add(v);
		}
		else
		    big_list.add(v);
	    }
	    Expr[] M = big_list.toArray(new Expr[big_list.size()]);
	    Vector<Expr> not_int = new Vector<Expr>();
	    Int lcm = Int.ONE;
	    for(int i = 0; i < M.length; i++)
	    {
		if(M[i].isInt())
		    lcm = Int.lcm(lcm, (Int) M[i]);
		else
		    not_int.add(M[i]);
	    }
	    Expr[] g;
	    Expr[] nt = Set.remove_dublicates(not_int.toArray(new Expr[not_int.size()]));
	    if(lcm.equals(Int.ONE))
		g = nt;
	    else
		g = Set.add(new Expr[] {lcm}, nt);
	    if(g.length == 1)
		return g[0];
	    g = merge_sort(g);
	    return new Expr(Operator.INTEGER_LCM, new Expr(Operator.LIST, g));
	}
	return new Expr(Operator.INTEGER_LCM, list);
    }

    private static Expr simplify_integer_extended_gcd(Expr list)
    {
	if(list.isList())
	{
	    Int[] l = Set.exprToIntArray(list.getOperands());
	    if(l != null)
	    {
		Int[] e = Int.extended_gcd(l);
		Int[] f = Set.first(e);
		return new Expr(Operator.LIST, e[e.length - 1], new Expr(Operator.LIST, f));
	    }
	}
	return new Expr(Operator.INTEGER_EXTENDED_GCD, list);
    }

    private static Expr simplify_integer_gcd(Expr list)
    {
	if(list.isList())
	{
	    Expr[] l = list.getOperands();
	    Vector<Expr> big_list = new Vector<Expr>();
	    for(int i = 0; i < l.length; i++)
	    {
		Expr v = l[i];
		if(v.getOperator().equals(Operator.INTEGER_GCD))
		{
		    Expr m = v.get(0);
		    if(m.isList())
		    {
			for(int j = 0; j < m.length(); j++)
			    big_list.add(m.get(j));
		    }
		    else
			big_list.add(v);
		}
		else
		    big_list.add(v);
	    }
	    Expr[] M = big_list.toArray(new Expr[big_list.size()]);
	    Vector<Expr> not_int = new Vector<Expr>();
	    Int gcd = Int.ZERO;
	    for(int i = 0; i < M.length; i++)
	    {
		if(M[i].isInt())
		    gcd = Int.gcd(gcd, (Int) M[i]);
		else
		    not_int.add(M[i]);
	    }
	    Expr[] g;
	    Expr[] nt = Set.remove_dublicates(not_int.toArray(new Expr[not_int.size()]));
	    if(gcd.equals(Int.ZERO))
		g = nt;
	    else
	    {
		if(gcd.equals(Int.ONE))
		    return Int.ONE;
		g = Set.add(new Expr[] {gcd}, nt);
	    }
	    if(g.length == 1)
		return g[0];
	    g = merge_sort(g);
	    return new Expr(Operator.INTEGER_GCD, new Expr(Operator.LIST, g));
	}
	return new Expr(Operator.INTEGER_GCD, list);
    }

    private static Expr simplify_poly_quotient(Expr[] e)
    {
	Expr a = Cancel.simplify(e[0], e[2]), b = Cancel.simplify(e[1], e[2]), x = e[2];
	if(e.length == 3)
	{
	    if(Poly.is_poly(a, x) && Poly.is_poly(b, x))
		return Cancel.polynomial_division_cancel(a, b, x)[0];
	}
	else
	{
	    Expr m = e[3];
	    if(m.getOperator().equals(Operator.ALGEBRAIC_EXTENSION))
	    {
		Expr[] alpha = m.get(0).isList() ? m.get(0).getOperands() : new Expr[] {m.get(0)};
		Expr[] p = m.get(1).isList() ? m.get(1).getOperands() : new Expr[] {m.get(1)};
		if(Poly.is_poly_Q(a, Set.add(new Expr[] {x}, alpha))
			&& Poly.is_poly_Q(b, Set.add(new Expr[] {x}, alpha)))
		    return AlgebraicNumberField.polynomial_quotient(a, b, x, p, alpha);
		else
		    throw new IllegalArgumentException(
			    "Cannot compute in a rational function field with algebraic extension");
	    }
	    if(m.getOperator().equals(Operator.MODULO))
	    {
		Int n = (Int) m.get(0);
		if(Poly.is_poly_Z(a, x) && Poly.is_poly_Z(b, x))
		    return BasicPoly.polynomial_quotient_p(a, b, x, n);
	    }
	}
	return new Expr(Operator.POLY_QUOTIENT, e);
    }

    private static Expr simplify_poly_remainder(Expr[] e)
    {
	Expr a = Cancel.simplify(e[0], e[2]), b = Cancel.simplify(e[1], e[2]), x = e[2];
	if(e.length == 3)
	{
	    if(Poly.is_poly(a, x) && Poly.is_poly(b, x))
		return Cancel.polynomial_division_cancel(a, b, x)[1];
	}
	else
	{
	    Expr m = e[3];
	    if(m.getOperator().equals(Operator.ALGEBRAIC_EXTENSION))
	    {
		Expr[] alpha = m.get(0).isList() ? m.get(0).getOperands() : new Expr[] {m.get(0)};
		Expr[] p = m.get(1).isList() ? m.get(1).getOperands() : new Expr[] {m.get(1)};
		if(Poly.is_poly_Q(a, Set.add(new Expr[] {x}, alpha))
			&& Poly.is_poly_Q(b, Set.add(new Expr[] {x}, alpha)))
		    return AlgebraicNumberField.polynomial_remainder(a, b, x, p, alpha);
		else
		    throw new IllegalArgumentException(
			    "Cannot compute in a rational function field with algebraic extension");
	    }
	    if(m.getOperator().equals(Operator.MODULO))
	    {
		Int n = (Int) m.get(0);
		if(Poly.is_poly_Z(a, x) && Poly.is_poly_Z(b, x))
		    return BasicPoly.polynomial_remainder_p(a, b, x, n);
	    }
	}
	return new Expr(Operator.POLY_REMAINDER, e);
    }

    private static Expr simplify_poly_degree(Expr a, Expr b)
    {
	if(Poly.is_poly(a, b))
	{
	    return Poly.degree(a, b);
	}
	return new Expr(Operator.POLY_DEGREE, a, b);
    }

    private static Expr simplify_adjoin(Expr a, Expr b)
    {
	if(a.isList() && b.isList())
	{
	    Expr[] list = Set.add(a.getOperands(), b.getOperands());
	    return new Expr(Operator.LIST, list);
	}
	return new Expr(Operator.ADJOIN, a, b);
    }

    private static Expr simplify_kind(Expr expr)
    {
	if(expr instanceof Symbolic)
	{
	    if(expr instanceof Int)
		return new Str("Int");
	    if(expr instanceof Decimal)
		return new Str("Decimal");
	    if(expr instanceof Rational)
		return new Str("Rational");
	    if(expr instanceof ModIntSym)
		return new Str("ModIntSym");
	    if(expr instanceof Str)
		return new Str("Str");
	    if(expr instanceof Constant)
		return new Str("Constant");
	    if(expr instanceof Var)
		return new Str("Var");
	    return new Str("Symbolic");
	}
	return new Str(expr.getOperator().getName());

    }

    private static Expr simplify_length(Expr expr)
    {
	if(expr instanceof Symbolic)
	    return Int.ZERO;
	return new Int(expr.length() + "");
    }

    private static Expr simplify_operand(Expr a, Expr b)
    {
	if(b.isInt())
	{
	    Int B = (Int) b;
	    int Bb = B.toInt();
	    if(Bb >= 0 && Bb < a.length())
		return a.get(Bb);
	}
	return new Expr(Operator.OPERAND, a, b);
    }

    private static Expr simplify_poly_coef(Expr[] a)
    {
	Expr u = a[0];
	Expr[] lx = getList(a[1]);
	Expr[] lj = getList(a[2]);
	if(lx.length == lj.length && isListOf(lj, Int.class))
	    return Poly.coefficient_poly(u, lx, castToInt(lj));
	return new Expr(Operator.POLY_COEF, a);

    }

    private static Expr simplify_i_quotient(Expr a, Expr b)
    {
	if(a instanceof Int && b instanceof Int)
	{
	    return ((Int) a).divide((Int) b);
	}
	return new Expr(Operator.I_QUOTIENT, a, b);
    }

    private static Expr simplify_modulus(Expr a, Expr b)
    {
	if(a instanceof Int && b instanceof Int)
	{
	    return ((Int) a).mod((Int) b);
	}
	return new Expr(Operator.MODULUS, a, b);
    }

    private static Expr simplify_structure_equality(Expr a, Expr b)
    {
	if(a.equals(b))
	    return Constant.TRUE;
	return Constant.FALSE;
    }

    private static Expr simplify_equal(Expr a, Expr b)
    {
	if(a.equals(b))
	    return Constant.TRUE;
	if(a.isNumerical() && b.isNumerical())
	{
	    int h = ((Numerical) a).compareTo((Numerical) b);
	    if(h != 0)
		return Constant.FALSE;
	}
	return new Expr(Operator.EQUAL, a, b);
    }

    private static Expr simplify_smaller(Expr a, Expr b)
    {
	if(a.isNumerical() && b.isNumerical())
	{
	    int h = ((Numerical) a).compareTo((Numerical) b);
	    if(h == -1)
		return Constant.TRUE;
	    else
		return Constant.FALSE;
	}
	return new Expr(Operator.SMALLER, a, b);
    }

    private static Expr simplify_commutative(Expr[] L, Operator p)
    {
	Expr[] e = new Expr[L.length];
	for(int i = 0; i < e.length; i++)
	    e[i] = L[i];
	return new Expr(p, merge_sort(e));
    }

    public static Expr simplify_intersection(Expr u)
    {
	Expr[] L = u.getOperands();
	if(Set.member(L, Constant.UNDEFINED))
	    return Constant.UNDEFINED;
	if(Set.member(L, Expr.EMPTY_SET))
	    return Expr.EMPTY_SET;
	if(L.length == 1)
	    return L[0];
	Expr[] v = simplify_intersection_rec(L);
	if(v.length == 1)
	    return v[0];
	if(v.length >= 2)
	    return new Expr(Operator.INTERSECTION, v);
	return Expr.FULL_SET;
    }

    private static Expr[] simplify_intersection_rec(Expr[] L)
    {
	if(L.length == 1)
	    return L;
	if(L.length == 2 && !L[0].getOperator().equals(Operator.INTERSECTION)
		&& !L[1].getOperator().equals(Operator.INTERSECTION))
	{
	    if(L[0].isSet() && L[1].isSet())
	    {
		if(L[0].length() == 1 && L[1].length() == 1)
		{
		    Expr[] list_1 = L[0].get(0).getOperands();
		    Expr[] list_2 = L[1].get(0).getOperands();
		    Expr intersect = new Expr(Operator.SET, new Expr(Operator.LIST, Set.intersect(
			    list_1, list_2)));
		    intersect = simplify_recursive(intersect);
		    return new Expr[] {intersect};
		}
		if(L[0].length() == 2 && L[1].length() == 2)
		{
		    Expr v_1 = L[0].get(0);
		    Expr v_2 = L[1].get(0);
		    Expr A_1 = L[0].get(1);
		    Expr A_2 = L[1].get(1);
		    Expr v;
		    if(v_1.equals(v_2))
			v = v_1;
		    else
			v = getNewVariables(1, v_1, v_2, A_1, A_2)[0];
		    A_1 = A_1.substitute(v_1, v);
		    A_2 = A_2.substitute(v_2, v);
		    Expr s = simplify_and(new Expr(Operator.AND, A_1, A_2));
		    Expr set = simplify_set(new Expr[] {v, s});
		    return new Expr[] {set};

		}

	    }

	    if(L[1].equals(L[0]))
		return new Expr[] {L[0]};
	    if(Expr.compare(L[1], L[0]) > 0)
		return new Expr[] {L[1], L[0]};
	    return L;
	}
	if(L.length == 2)
	{
	    if(L[0].getOperator().equals(Operator.INTERSECTION)
		    && L[1].getOperator().equals(Operator.INTERSECTION))
	    {
		return merge_intersections(L[0].getOperands(), L[1].getOperands());
	    }
	    if(L[0].getOperator().equals(Operator.INTERSECTION)
		    && !L[1].getOperator().equals(Operator.INTERSECTION))
	    {
		return merge_intersections(L[0].getOperands(), new Expr[] {L[1]});
	    }
	    if(!L[0].getOperator().equals(Operator.INTERSECTION)
		    && L[1].getOperator().equals(Operator.INTERSECTION))
	    {
		return merge_intersections(new Expr[] {L[0]}, L[1].getOperands());
	    }
	}
	if(L.length > 2)
	{

	    Expr[] R = new Expr[L.length - 1];
	    for(int i = 0; i < R.length; i++)
		R[i] = L[i + 1];
	    Expr[] w = simplify_intersection_rec(R);
	    Expr[] simp;
	    if(L[0].getOperator().equals(Operator.INTERSECTION))
		simp = merge_intersections(L[0].getOperands(), w);
	    else
		simp = merge_intersections(new Expr[] {L[0]}, w);
	    if(!Set.equal(L, simp))
		return simplify_intersection_rec(simp);
	    return simp;
	}
	return null; // Never ever!
    }

    private static Expr[] merge_intersections(Expr[] p, Expr[] q)
    {
	if(q.length == 0)
	    return p;
	if(p.length == 0)
	    return q;
	Expr p_1 = p[0];
	Expr q_1 = q[0];
	Expr[] R_p = new Expr[p.length - 1];
	for(int i = 0; i < R_p.length; i++)
	    R_p[i] = p[i + 1];
	Expr[] R_q = new Expr[q.length - 1];
	for(int i = 0; i < R_q.length; i++)
	    R_q[i] = q[i + 1];
	Expr[] h = simplify_intersection_rec(new Expr[] {p_1, q_1});
	if(h.length == 0)
	    return merge_intersections(R_p, R_q);
	if(h.length == 1)
	{
	    Expr[] k = merge_intersections(R_p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = h[0];
	    return tmp;
	}
	if(h.length == 2 && h[0].equals(p_1) && h[1].equals(q_1))
	{
	    Expr[] k = merge_intersections(R_p, q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = p_1;
	    return tmp;
	}
	else
	{
	    Expr[] k = merge_intersections(p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = q_1;
	    return tmp;
	}
    }

    public static Expr simplify_union(Expr u)
    {
	Expr[] L = u.getOperands();
	if(Set.member(L, Constant.UNDEFINED))
	    return Constant.UNDEFINED;
	if(L.length == 1)
	    return L[0];
	Expr[] v = simplify_union_rec(L);
	if(v.length == 1)
	    return v[0];
	if(v.length >= 2)
	    return new Expr(Operator.UNION, v);
	return Expr.EMPTY_SET;
    }

    private static Expr[] simplify_union_rec(Expr[] L)
    {
	if(L.length == 1)
	    return L;
	if(L.length == 2 && !L[0].getOperator().equals(Operator.UNION)
		&& !L[1].getOperator().equals(Operator.UNION))
	{
	    if(L[0].isSet() && L[1].isSet())
	    {
		if(L[0].length() == 1 && L[1].length() == 1)
		{
		    Expr[] list_1 = L[0].get(0).getOperands();
		    Expr[] list_2 = L[1].get(0).getOperands();
		    Expr union = new Expr(Operator.SET, new Expr(Operator.LIST, Set.union(list_1,
			    list_2)));
		    union = simplify_recursive(union);
		    return new Expr[] {union};
		}
		if(L[0].length() == 2 && L[1].length() == 2)
		{
		    Expr v_1 = L[0].get(0);
		    Expr v_2 = L[1].get(0);
		    Expr A_1 = L[0].get(1);
		    Expr A_2 = L[1].get(1);
		    Expr v;
		    if(v_1.equals(v_2))
			v = v_1;
		    else
			v = getNewVariables(1, v_1, v_2, A_1, A_2)[0];
		    A_1 = A_1.substitute(v_1, v);
		    A_2 = A_2.substitute(v_2, v);
		    Expr s = simplify_or(new Expr(Operator.OR, A_1, A_2));
		    Expr set = simplify_set(new Expr[] {v, s});
		    return new Expr[] {set};

		}

	    }
	    if(L[0].equals(Expr.EMPTY_SET))
		return new Expr[] {L[1]};
	    if(L[1].equals(Expr.EMPTY_SET))
		return new Expr[] {L[0]};
	    if(L[1].equals(L[0]))
		return new Expr[] {L[0]};
	    if(Expr.compare(L[1], L[0]) > 0)
		return new Expr[] {L[1], L[0]};
	    return L;
	}
	if(L.length == 2)
	{
	    if(L[0].getOperator().equals(Operator.UNION)
		    && L[1].getOperator().equals(Operator.UNION))
	    {
		return merge_unions(L[0].getOperands(), L[1].getOperands());
	    }
	    if(L[0].getOperator().equals(Operator.UNION)
		    && !L[1].getOperator().equals(Operator.UNION))
	    {
		return merge_unions(L[0].getOperands(), new Expr[] {L[1]});
	    }
	    if(!L[0].getOperator().equals(Operator.UNION)
		    && L[1].getOperator().equals(Operator.UNION))
	    {
		return merge_unions(new Expr[] {L[0]}, L[1].getOperands());
	    }
	}
	if(L.length > 2)
	{

	    Expr[] R = new Expr[L.length - 1];
	    for(int i = 0; i < R.length; i++)
		R[i] = L[i + 1];
	    Expr[] w = simplify_union_rec(R);
	    Expr[] simp;
	    if(L[0].getOperator().equals(Operator.UNION))
		simp = merge_unions(L[0].getOperands(), w);
	    else
		simp = merge_unions(new Expr[] {L[0]}, w);
	    if(!Set.equal(L, simp))
		return simplify_union_rec(simp);
	    return simp;
	}
	return null; // Never ever!
    }

    private static Expr[] merge_unions(Expr[] p, Expr[] q)
    {
	if(q.length == 0)
	    return p;
	if(p.length == 0)
	    return q;
	Expr p_1 = p[0];
	Expr q_1 = q[0];
	Expr[] R_p = new Expr[p.length - 1];
	for(int i = 0; i < R_p.length; i++)
	    R_p[i] = p[i + 1];
	Expr[] R_q = new Expr[q.length - 1];
	for(int i = 0; i < R_q.length; i++)
	    R_q[i] = q[i + 1];
	Expr[] h = simplify_union_rec(new Expr[] {p_1, q_1});
	if(h.length == 0)
	    return merge_unions(R_p, R_q);
	if(h.length == 1)
	{
	    Expr[] k = merge_unions(R_p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = h[0];
	    return tmp;
	}
	if(h.length == 2 && h[0].equals(p_1) && h[1].equals(q_1))
	{
	    Expr[] k = merge_unions(R_p, q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = p_1;
	    return tmp;
	}
	else
	{
	    Expr[] k = merge_unions(p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = q_1;
	    return tmp;
	}
    }

    public static Expr simplify_or(Expr u)
    {
	Expr[] L = u.getOperands();
	if(Set.member(L, Constant.UNDEFINED))
	    return Constant.UNDEFINED;
	if(Set.member(L, Constant.TRUE))
	    return Constant.TRUE;
	if(L.length == 1)
	    return L[0];
	Expr[] v = simplify_or_rec(L);
	if(v.length == 1)
	    return v[0];
	if(v.length >= 2)
	    return new Expr(Operator.OR, v);
	return Constant.FALSE;
    }

    private static Expr[] simplify_or_rec(Expr[] L)
    {
	if(L.length == 1)
	    return L;
	if(Set.member(L, Constant.TRUE))
	    return new Expr[] {Constant.TRUE};

	if(L.length == 2 && !L[0].getOperator().equals(Operator.OR)
		&& !L[1].getOperator().equals(Operator.OR))
	{
	    if(L[0].isLogicalConstant() && L[1].isLogicalConstant())
	    {
		if(L[0].equals(Constant.TRUE) || L[0].equals(Constant.TRUE))
		    return new Expr[] {Constant.TRUE};
		return new Expr[] {Constant.FALSE};
	    }
	    if(L[0].equals(Constant.FALSE))
		return new Expr[] {L[1]};
	    if(L[1].equals(Constant.FALSE))
		return new Expr[] {L[0]};
	    if(L[1].equals(new Expr(Operator.NOT, L[0])))
		return new Expr[] {Constant.TRUE};
	    if(L[0].equals(new Expr(Operator.NOT, L[1])))
		return new Expr[] {Constant.TRUE};
	    if(L[1].equals(L[0]))
		return new Expr[] {L[0]};
	    if(Expr.compare(L[1], L[0]) > 0)
		return new Expr[] {L[1], L[0]};
	    return L;
	}
	if(L.length == 2)
	{
	    if(L[0].getOperator().equals(Operator.OR) && L[1].getOperator().equals(Operator.OR))
	    {
		return merge_ors(L[0].getOperands(), L[1].getOperands());
	    }
	    if(L[0].getOperator().equals(Operator.OR) && !L[1].getOperator().equals(Operator.OR))
	    {
		return merge_ors(L[0].getOperands(), new Expr[] {L[1]});
	    }
	    if(!L[0].getOperator().equals(Operator.OR) && L[1].getOperator().equals(Operator.OR))
	    {
		return merge_ors(new Expr[] {L[0]}, L[1].getOperands());
	    }
	}
	if(L.length > 2)
	{
	    for(int i = 0; i < L.length; i++)
	    {
		if(Set.member(L, new Expr(Operator.NOT, L[i])))
		    return new Expr[] {Constant.TRUE};
	    }
	    Expr[] R = new Expr[L.length - 1];
	    for(int i = 0; i < R.length; i++)
		R[i] = L[i + 1];
	    Expr[] w = simplify_or_rec(R);
	    Expr[] simp;
	    if(L[0].getOperator().equals(Operator.OR))
		simp = merge_ors(L[0].getOperands(), w);
	    else
		simp = merge_ors(new Expr[] {L[0]}, w);
	    if(!Set.equal(L, simp))
		return simplify_or_rec(simp);
	    return simp;
	}
	return null;
    }

    private static Expr[] merge_ors(Expr[] p, Expr[] q)
    {
	if(q.length == 0)
	    return p;
	if(p.length == 0)
	    return q;
	Expr p_1 = p[0];
	Expr q_1 = q[0];
	Expr[] R_p = new Expr[p.length - 1];
	for(int i = 0; i < R_p.length; i++)
	    R_p[i] = p[i + 1];
	Expr[] R_q = new Expr[q.length - 1];
	for(int i = 0; i < R_q.length; i++)
	    R_q[i] = q[i + 1];
	Expr[] h = simplify_or_rec(new Expr[] {p_1, q_1});
	if(h.length == 0)
	    return merge_ors(R_p, R_q);
	if(h.length == 1)
	{
	    Expr[] k = merge_ors(R_p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = h[0];
	    return tmp;
	}
	if(h.length == 2 && h[0].equals(p_1) && h[1].equals(q_1))
	{
	    Expr[] k = merge_ors(R_p, q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = p_1;
	    return tmp;
	}
	else
	{
	    Expr[] k = merge_ors(p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = q_1;
	    return tmp;
	}
    }

    public static Expr simplify_and(Expr u)
    {
	Expr[] L = u.getOperands();
	if(Set.member(L, Constant.UNDEFINED))
	    return Constant.UNDEFINED;
	if(Set.member(L, Constant.FALSE))
	    return Constant.FALSE;
	if(L.length == 1)
	    return L[0];
	Expr[] v = simplify_and_rec(L);
	if(v.length == 1)
	    return v[0];
	if(v.length >= 2)
	    return new Expr(Operator.AND, v);
	return Constant.TRUE;
    }

    private static Expr[] simplify_and_rec(Expr[] L)
    {
	if(L.length == 1)
	    return L;
	if(Set.member(L, Constant.FALSE))
	    return new Expr[] {Constant.FALSE};
	if(L.length == 2 && !L[0].getOperator().equals(Operator.AND)
		&& !L[1].getOperator().equals(Operator.AND))
	{
	    if(L[0].isLogicalConstant() && L[1].isLogicalConstant())
	    {
		if(L[0].equals(Constant.TRUE) && L[0].equals(Constant.TRUE))
		    return new Expr[] {Constant.TRUE};
		return new Expr[] {Constant.FALSE};
	    }
	    if(L[0].equals(Constant.TRUE))
		return new Expr[] {L[1]};
	    if(L[1].equals(Constant.TRUE))
		return new Expr[] {L[0]};
	    if(L[1].equals(new Expr(Operator.NOT, L[0])))
		return new Expr[] {Constant.FALSE};
	    if(L[0].equals(new Expr(Operator.NOT, L[1])))
		return new Expr[] {Constant.FALSE};
	    if(L[1].equals(L[0]))
		return new Expr[] {L[0]};
	    if(Expr.compare(L[1], L[0]) > 0)
		return new Expr[] {L[1], L[0]};
	    return L;
	}
	if(L.length == 2)
	{
	    if(L[0].getOperator().equals(Operator.AND) && L[1].getOperator().equals(Operator.AND))
	    {
		return merge_ands(L[0].getOperands(), L[1].getOperands());
	    }
	    if(L[0].getOperator().equals(Operator.AND) && !L[1].getOperator().equals(Operator.AND))
	    {
		return merge_ands(L[0].getOperands(), new Expr[] {L[1]});
	    }
	    if(!L[0].getOperator().equals(Operator.AND) && L[1].getOperator().equals(Operator.AND))
	    {
		return merge_ands(new Expr[] {L[0]}, L[1].getOperands());
	    }
	}
	if(L.length > 2)
	{
	    for(int i = 0; i < L.length; i++)
	    {
		if(Set.member(L, new Expr(Operator.NOT, L[i])))
		    return new Expr[] {Constant.FALSE};
	    }

	    Expr[] R = new Expr[L.length - 1];
	    for(int i = 0; i < R.length; i++)
		R[i] = L[i + 1];
	    Expr[] w = simplify_and_rec(R);
	    Expr[] simp;
	    if(L[0].getOperator().equals(Operator.OR))
		simp = merge_ands(L[0].getOperands(), w);
	    else
		simp = merge_ands(new Expr[] {L[0]}, w);
	    if(!Set.equal(L, simp))
		return simplify_and_rec(simp);
	    return simp;
	}
	return null;
    }

    private static Expr[] merge_ands(Expr[] p, Expr[] q)
    {
	if(q.length == 0)
	    return p;
	if(p.length == 0)
	    return q;
	Expr p_1 = p[0];
	Expr q_1 = q[0];
	Expr[] R_p = new Expr[p.length - 1];
	for(int i = 0; i < R_p.length; i++)
	    R_p[i] = p[i + 1];
	Expr[] R_q = new Expr[q.length - 1];
	for(int i = 0; i < R_q.length; i++)
	    R_q[i] = q[i + 1];
	Expr[] h = simplify_and_rec(new Expr[] {p_1, q_1});
	if(h.length == 0)
	    return merge_ands(R_p, R_q);
	if(h.length == 1)
	{
	    Expr[] k = merge_ands(R_p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = h[0];
	    return tmp;
	}
	if(h.length == 2 && h[0].equals(p_1) && h[1].equals(q_1))
	{
	    Expr[] k = merge_ands(R_p, q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = p_1;
	    return tmp;
	}
	else
	{
	    Expr[] k = merge_ands(p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = q_1;
	    return tmp;
	}
    }

    public static Expr simplify_not(Expr u)
    {
	Expr L = u;
	if(L.equals(Constant.TRUE))
	    return Constant.FALSE;
	if(L.equals(Constant.FALSE))
	    return Constant.TRUE;
	if(L.getOperator().equals(Operator.NOT))
	    return L.get(0);
	if(L.getOperator().equals(Operator.FORALL))
	{
	    Expr A = simplify_not(L.get(2));
	    return new Expr(Operator.EXISTS, L.get(0), L.get(1), A);
	}
	if(L.getOperator().equals(Operator.EXISTS))
	{
	    Expr A = simplify_not(L.get(2));
	    return new Expr(Operator.FORALL, L.get(0), L.get(1), A);
	}
	if(L.getOperator().equals(Operator.SMALLER))
	{
	    return simplify_bigger_equal(L.get(0), L.get(1));
	}
	if(L.getOperator().equals(Operator.BIGGER))
	{
	    return simplify_smaller_equal(L.get(0), L.get(1));
	}
	if(L.getOperator().equals(Operator.BIGGER_EQUAL))
	{
	    return simplify_smaller(L.get(0), L.get(1));
	}
	if(L.getOperator().equals(Operator.SMALLER_EQUAL))
	{
	    return simplify_bigger(L.get(0), L.get(1));
	}
	return new Expr(Operator.NOT, u);
    }

    public static Expr simplify_sum(Expr u)
    {
	Expr[] L = u.getOperands();
	if(Set.member(L, Constant.UNDEFINED))
	    return Constant.UNDEFINED;
	if(L.length == 1)
	    return L[0];
	Expr[] v = simplify_sum_rec(L);
	if(v.length == 1)
	    return v[0];
	if(v.length >= 2)
	    return new Expr(Operator.ADD, v);
	else
	    return Int.ZERO;
    }

    private static Expr[] simplify_sum_rec(Expr[] L)
    {
	if(L.length == 2 && !L[0].isSum() && !L[1].isSum())
	{
	    if(L[0].isNumerical() && L[1].isNumerical())
	    {
		Expr P = ((Numerical) L[0]).add((Numerical) L[1]);
		if(P.equals(Int.ZERO))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[0] instanceof ModIntSym && L[1] instanceof ModIntSym)
	    {
		ModIntSym a = (ModIntSym) L[0];
		ModIntSym b = (ModIntSym) L[1];
		if(a.getModulus().equals(b.getModulus()))
		{
		    Expr P = a.add(b);
		    if(P.equals(new ModIntSym(Int.ZERO, a.getModulus())))
			return new Expr[] {};
		    return new Expr[] {P};
		}
	    }
	    if(L[0] instanceof Int && L[1] instanceof ModIntSym)
	    {
		Int a = (Int) L[0];
		ModIntSym b = (ModIntSym) L[1];
		Expr P = new ModIntSym(b.toInt().add(a), b.getModulus());
		if(P.equals(new ModIntSym(Int.ZERO, b.getModulus())))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[1] instanceof Int && L[0] instanceof ModIntSym)
	    {
		Int a = (Int) L[1];
		ModIntSym b = (ModIntSym) L[0];

		Expr P = new ModIntSym(b.toInt().add(a), b.getModulus());
		if(P.equals(new ModIntSym(Int.ZERO, b.getModulus())))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[0] instanceof ModIntNon && L[1] instanceof ModIntNon)
	    {
		ModIntNon a = (ModIntNon) L[0];
		ModIntNon b = (ModIntNon) L[1];
		if(a.getModulus().equals(b.getModulus()))
		{
		    Expr P = a.add(b);
		    if(P.equals(new ModIntNon(Int.ZERO, a.getModulus())))
			return new Expr[] {};
		    return new Expr[] {P};
		}
	    }
	    if(L[0] instanceof Int && L[1] instanceof ModIntNon)
	    {
		Int a = (Int) L[0];
		ModIntNon b = (ModIntNon) L[1];
		Expr P = new ModIntNon(b.toInt().add(a), b.getModulus());
		if(P.equals(new ModIntNon(Int.ZERO, b.getModulus())))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[1] instanceof Int && L[0] instanceof ModIntNon)
	    {
		Int a = (Int) L[1];
		ModIntNon b = (ModIntNon) L[0];

		Expr P = new ModIntNon(b.toInt().add(a), b.getModulus());
		if(P.equals(new ModIntNon(Int.ZERO, b.getModulus())))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[0].getOperator().equals(Operator.PSERIES)
		    && L[1].getOperator().equals(Operator.PSERIES))
	    {
		if(L[0].get(1).equals(L[1].get(1)))
		{
		    Series c = new Series(L[0].get(0).getOperands()).add(new Series(L[1].get(0)
			    .getOperands()));
		    return new Expr[] {new Expr(Operator.PSERIES, new Expr(Operator.LIST,
			    c.getCoefs()), L[0].get(1))};
		}
	    }
	    if(L[0].equals(Int.ZERO))
		return new Expr[] {L[1]};
	    if(L[1].equals(Int.ZERO))
		return new Expr[] {L[0]};
	    Expr[] be_1 = constant_mod_term(L[0]);
	    Expr[] be_2 = constant_mod_term(L[1]);
	    if(be_1[1].equals(be_2[1]))
	    {
		Expr S = simplify_sum(new Expr(Operator.ADD, new Expr[] {be_1[0], be_2[0]}));
		Expr P = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {be_1[1], S}));
		if(P.equals(Int.ZERO))
		    return new Expr[] {};
		else
		    return new Expr[] {P};
	    }

	    if(L[1].isList() && L[0].isList() && L[1].length() == L[0].length())
	    {
		Expr[] p = new Expr[L[1].length()];
		for(int i = 0; i < p.length; i++)
		    p[i] = simplify_sum(new Expr(Operator.ADD,
			    new Expr[] {L[0].get(i), L[1].get(i)}));
		return new Expr[] {new Expr(Operator.LIST, p)};
	    }
	    if(L[0].isMatrix() && L[1].isMatrix())
	    {

		Expr[][] C = Matrix.add(Set.toExprArray(L[0].get(0)), Set.toExprArray(L[1].get(0)));
		return new Expr[] {new Expr(Operator.MATRIX, Set.toList(C))};
	    }
	    if(Expr.compare(L[1], L[0]) > 0)
		return new Expr[] {L[1], L[0]};
	    return L;
	}
	if(L.length == 2)
	{
	    if(L[0].isSum() && L[1].isSum())
	    {
		return merge_sums(L[0].getOperands(), L[1].getOperands());
	    }
	    if(L[0].isSum() && !L[1].isSum())
	    {
		return merge_sums(L[0].getOperands(), new Expr[] {L[1]});
	    }
	    if(!L[0].isSum() && L[1].isSum())
	    {
		return merge_sums(new Expr[] {L[0]}, L[1].getOperands());
	    }

	}
	if(L.length > 2)
	{
	    Expr[] R = new Expr[L.length - 1];
	    for(int i = 0; i < R.length; i++)
		R[i] = L[i + 1];
	    Expr[] w = simplify_sum_rec(R);
	    if(L[0].isSum())
		return merge_sums(L[0].getOperands(), w);
	    else
		return merge_sums(new Expr[] {L[0]}, w);
	}

	return null;
    }

    private static Expr[] merge_sums(Expr[] p, Expr[] q)
    {
	if(q.length == 0)
	    return p;
	if(p.length == 0)
	    return q;
	Expr p_1 = p[0];
	Expr q_1 = q[0];
	Expr[] R_p = new Expr[p.length - 1];
	for(int i = 0; i < R_p.length; i++)
	    R_p[i] = p[i + 1];
	Expr[] R_q = new Expr[q.length - 1];
	for(int i = 0; i < R_q.length; i++)
	    R_q[i] = q[i + 1];
	Expr[] h = simplify_sum_rec(new Expr[] {p_1, q_1});
	if(h.length == 0)
	    return merge_sums(R_p, R_q);
	if(h.length == 1)
	{
	    Expr[] k = merge_sums(R_p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = h[0];
	    return tmp;
	}
	if(h.length == 2 && h[0].equals(p_1) && h[1].equals(q_1))
	{
	    Expr[] k = merge_sums(R_p, q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = p_1;
	    return tmp;
	}
	else
	{
	    Expr[] k = merge_sums(p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = q_1;
	    return tmp;
	}

    }

    public static Expr simplify_product(Expr u)
    {
	Expr[] L = u.getOperands();
	if(Set.member(L, Constant.UNDEFINED))
	    return Constant.UNDEFINED;
	if(Set.member(L, Int.ZERO) && !Operator.hasOperator(L, Operator.MATRIX))
	    return Int.ZERO;
	if(L.length == 1)
	    return L[0];
	Expr[] v = simplify_product_rec(L);
	if(v.length == 1)
	    return v[0];
	if(v.length == 2 && v[0].isNumerical() && v[1].isSum() && expand_constants)
	{
	    Expr[] s = new Expr[v[1].length()];
	    for(int i = 0; i < s.length; i++)
		s[i] = simplify_product(new Expr(Operator.MULTIPLY, v[0], v[1].get(i)));
	    return simplify_sum(new Expr(Operator.ADD, s));
	}
	if(v.length >= 2)
	{
	    if(!simplify_rational_int_powers)
		return new Expr(Operator.MULTIPLY, v);
	    else
		return simplify_rational_int_powers_in_product(v);
	}
	else
	    return Int.ONE;
    }

    private static Expr[] simplify_product_rec(Expr[] L)
    {
	if(L.length == 1)
	{
	    if(L[0].equals(Int.ONE))
		return new Expr[] {};
	    return L;
	}
	if(L.length == 2 && !L[0].getOperator().equals(Operator.MULTIPLY)
		&& !L[1].getOperator().equals(Operator.MULTIPLY))
	{
	    if(L[0].isNumerical() && L[1].isNumerical())
	    {
		Expr P = ((Numerical) L[0]).mul((Numerical) L[1]);
		if(P.equals(Int.ONE))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[0] instanceof ModIntSym && L[1] instanceof ModIntSym)
	    {
		ModIntSym a = (ModIntSym) L[0];
		ModIntSym b = (ModIntSym) L[1];
		if(a.getModulus().equals(b.getModulus()))
		{
		    Expr P = a.mul(b);
		    if(P.equals(new ModIntSym(Int.ONE, a.getModulus())))
			return new Expr[] {};
		    return new Expr[] {P};
		}
	    }
	    if(L[0] instanceof Int && L[1] instanceof ModIntSym)
	    {
		Int a = (Int) L[0];
		ModIntSym b = (ModIntSym) L[1];

		Expr P = new ModIntSym(b.toInt().mul(a), b.getModulus());
		if(P.equals(new ModIntSym(Int.ONE, b.getModulus())))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[1] instanceof Int && L[0] instanceof ModIntSym)
	    {
		Int a = (Int) L[1];
		ModIntSym b = (ModIntSym) L[0];

		Expr P = new ModIntSym(b.toInt().mul(a), b.getModulus());
		if(P.equals(new ModIntSym(Int.ONE, b.getModulus())))
		    return new Expr[] {};
		return new Expr[] {P};
	    }

	    if(L[0] instanceof ModIntNon && L[1] instanceof ModIntNon)
	    {
		ModIntNon a = (ModIntNon) L[0];
		ModIntNon b = (ModIntNon) L[1];
		if(a.getModulus().equals(b.getModulus()))
		{
		    Expr P = a.mul(b);
		    if(P.equals(new ModIntNon(Int.ONE, a.getModulus())))
			return new Expr[] {};
		    return new Expr[] {P};
		}
	    }
	    if(L[0] instanceof Int && L[1] instanceof ModIntNon)
	    {
		Int a = (Int) L[0];
		ModIntNon b = (ModIntNon) L[1];

		Expr P = new ModIntNon(b.toInt().mul(a), b.getModulus());
		if(P.equals(new ModIntNon(Int.ONE, b.getModulus())))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[1] instanceof Int && L[0] instanceof ModIntNon)
	    {
		Int a = (Int) L[1];
		ModIntNon b = (ModIntNon) L[0];

		Expr P = new ModIntNon(b.toInt().mul(a), b.getModulus());
		if(P.equals(new ModIntNon(Int.ONE, b.getModulus())))
		    return new Expr[] {};
		return new Expr[] {P};
	    }
	    if(L[0].getOperator().equals(Operator.BIG_O)
		    && L[1].getOperator().equals(Operator.BIG_O))
	    {
		if(L[0].get(1).equals(L[1].get(1)))
		{
		    Expr P = simplify_product(new Expr(Operator.MULTIPLY, L[0].get(0), L[1].get(0)));
		    Expr O = simplify_big_o(P, L[0].get(1));
		    if(O.equals(Int.ONE))
			return new Expr[] {};
		    return new Expr[] {O};
		}
	    }
	    if(L[0].getOperator().equals(Operator.BIG_O) && L[1].isFreeOf(L[0].get(1)))
	    {
		return new Expr[] {L[0]};
	    }
	    if(L[1].getOperator().equals(Operator.BIG_O) && L[0].isFreeOf(L[1].get(1)))
	    {
		return new Expr[] {L[1]};
	    }

	    // Gaussian Rational Number Arithmetic
	    Numerical[] gr_0 = gaussian_rational(L[0]);
	    Numerical[] gr_1 = gaussian_rational(L[1]);

	    if(gr_0 != null && gr_1 != null)
	    {
		Numerical[] j = Numerical.mul(gr_0, gr_1);
		if(j[0].equals(Int.ZERO) && j[1].equals(Int.ZERO))
		    return new Expr[] {Int.ZERO};
		if(j[0].equals(Int.ONE) && j[1].equals(Int.ZERO))
		    return new Expr[] {};
		if(j[1].equals(Int.ZERO))
		    return new Expr[] {j[0]};
		if(j[1].equals(Int.ONE) && j[0].equals(Int.ZERO))
		    return new Expr[] {Constant.I};
		if(j[1].equals(Int.ONE))
		    return new Expr[] {new Expr(Operator.ADD, new Expr[] {j[0], Constant.I})};
		if(j[0].equals(Int.ZERO))
		    return new Expr[] {j[1], Constant.I};
		return new Expr[] {new Expr(Operator.ADD, new Expr[] {j[0],
			new Expr(Operator.MULTIPLY, new Expr[] {j[1], Constant.I})})};
	    }

	    if(L[1].isList() && L[0].isList() && L[1].length() == L[0].length())
	    {
		Expr[] p = new Expr[L[1].length()];
		for(int i = 0; i < p.length; i++)
		    p[i] = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {L[0].get(i),
			    L[1].get(i)}));
		return new Expr[] {new Expr(Operator.LIST, p)};
	    }
	    if(L[0].isList() && !L[1].isList())
	    {
		Expr[] p = new Expr[L[0].length()];
		for(int i = 0; i < p.length; i++)
		    p[i] = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {L[0].get(i),
			    L[1]}));
		return new Expr[] {new Expr(Operator.LIST, p)};
	    }
	    if(L[1].isList() && !L[0].isList())
	    {
		Expr[] p = new Expr[L[1].length()];
		for(int i = 0; i < p.length; i++)
		    p[i] = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {L[0],
			    L[1].get(i)}));
		return new Expr[] {new Expr(Operator.LIST, p)};
	    }
	    if(L[0].isMatrix() && L[1].isMatrix())
	    {
		Expr[][] C = Matrix.multiply(Set.toExprArray(L[0].get(0)),
			Set.toExprArray(L[1].get(0)));
		return new Expr[] {new Expr(Operator.MATRIX, Set.toList(C))};
	    }
	    if(L[0].isMatrix() && !L[1].isMatrix())
	    {
		Expr[][] C = Matrix.multiply_scalar(L[1], Set.toExprArray(L[0].get(0)));
		return new Expr[] {new Expr(Operator.MATRIX, Set.toList(C))};
	    }
	    if(!L[0].isMatrix() && L[1].isMatrix())
	    {
		Expr[][] C = Matrix.multiply_scalar(L[0], Set.toExprArray(L[1].get(0)));
		return new Expr[] {new Expr(Operator.MATRIX, Set.toList(C))};
	    }
	    if(L[0].getOperator().equals(Operator.PSERIES)
		    && L[1].getOperator().equals(Operator.PSERIES))
	    {
		if(L[0].get(1).equals(L[1].get(1)))
		{
		    Series c = new Series(L[0].get(0).getOperands()).mul(new Series(L[1].get(0)
			    .getOperands()));
		    return new Expr[] {new Expr(Operator.PSERIES, new Expr(Operator.LIST,
			    c.getCoefs()), L[0].get(1))};
		}
	    }
	    if(L[0].equals(Int.ONE))
		return new Expr[] {L[1]};
	    if(L[1].equals(Int.ONE))
		return new Expr[] {L[0]};
	    Expr[] be_1 = base_exp(L[0]);
	    Expr[] be_2 = base_exp(L[1]);

	    if(be_1[0].equals(be_2[0]))
	    {
		Expr S = simplify_sum(new Expr(Operator.ADD, new Expr[] {be_1[1], be_2[1]}));
		Expr P = simplify_power(new Expr(Operator.POWER, new Expr[] {be_1[0], S}));
		if(P.equals(Int.ONE))
		    return new Expr[] {};
		else
		    return new Expr[] {P};
	    }
	    // Ints with same powers are collected together: 2^(1/3)*5^(1/3)*4
	    // -> 10^(1/3)*4
	    if(be_1[0] instanceof Int && be_2[0] instanceof Int)
	    {
		if(((Int) be_1[0]).compareTo(Int.ZERO) == 1
			&& ((Int) be_2[0]).compareTo(Int.ZERO) == 1)
		{
		    if(be_1[1].equals(be_2[1]))
		    {
			Expr P = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {be_1[0],
				be_2[0]}));
			if(P.equals(Int.ONE))
			    return new Expr[] {};
			else
			{
			    // TODO: 2/15*2^(1/3)*3^(1/3)*5^(1/3)*7^(2/3) is not
			    // merged appropriately
			    Expr r = simplify_power(new Expr(Operator.POWER,
				    new Expr[] {P, be_1[1]}));
			    r = simplify_product(new Expr(Operator.MULTIPLY, r));
			    System.out.println("r: " + r);
			    if(r.isProduct())
				return r.getOperands();
			    else
				return new Expr[] {r};
			}

		    }
		    else
		    {
			// Factor out the gcd if the powers are not the same
			Int a = (Int) be_1[0];
			Int b = (Int) be_2[0];
			Int c = Int.gcd(a, b);
			if(!c.equals(Int.ONE))
			{
			    Expr exp = simplify_sum(new Expr(Operator.ADD, new Expr[] {be_1[1],
				    be_2[1]}));
			    Expr f = simplify_power(new Expr(Operator.POWER, new Expr[] {c, exp}));
			    a = a.divide(c);
			    b = b.divide(c);
			    Expr a_t = simplify_power(new Expr(Operator.POWER, new Expr[] {a,
				    be_1[1]}));
			    Expr b_t = simplify_power(new Expr(Operator.POWER, new Expr[] {b,
				    be_2[1]}));
			    Expr d = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {a_t,
				    b_t, f}));
			    if(d.equals(Int.ONE))
				return new Expr[] {};
			    return d.getOperands();
			}
		    }

		}

	    }
	    if(Expr.compare(L[1], L[0]) > 0)
		return new Expr[] {L[1], L[0]};
	    return L;
	}
	if(L.length == 2)
	{
	    if(L[0].getOperator().equals(Operator.MULTIPLY)
		    && L[1].getOperator().equals(Operator.MULTIPLY))
	    {
		return merge_products(L[0].getOperands(), L[1].getOperands());
	    }
	    if(L[0].getOperator().equals(Operator.MULTIPLY)
		    && !L[1].getOperator().equals(Operator.MULTIPLY))
	    {
		return merge_products(L[0].getOperands(), new Expr[] {L[1]});
	    }
	    if(!L[0].getOperator().equals(Operator.MULTIPLY)
		    && L[1].getOperator().equals(Operator.MULTIPLY))
	    {
		return merge_products(new Expr[] {L[0]}, L[1].getOperands());
	    }
	}
	if(L.length > 2)
	{
	    Expr[] R = new Expr[L.length - 1];
	    for(int i = 0; i < R.length; i++)
		R[i] = L[i + 1];
	    Expr[] w = simplify_product_rec(R);
	    if(L[0].getOperator().equals(Operator.MULTIPLY))
		return merge_products(L[0].getOperands(), w);
	    else
		return merge_products(new Expr[] {L[0]}, w);
	}
	return null;
    }

    private static Expr[] merge_products(Expr[] p, Expr[] q)
    {
	if(q.length == 0)
	    return p;
	if(p.length == 0)
	    return q;
	Expr p_1 = p[0];
	Expr q_1 = q[0];
	Expr[] R_p = new Expr[p.length - 1];
	for(int i = 0; i < R_p.length; i++)
	    R_p[i] = p[i + 1];
	Expr[] R_q = new Expr[q.length - 1];
	for(int i = 0; i < R_q.length; i++)
	    R_q[i] = q[i + 1];
	Expr[] h = simplify_product_rec(new Expr[] {p_1, q_1});
	if(h.length == 0)
	    return merge_products(R_p, R_q);
	if(h.length == 1)
	{
	    Expr[] k = merge_products(R_p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = h[0];
	    return tmp;
	}
	if(h.length == 2 && h[0].equals(p_1) && h[1].equals(q_1))
	{
	    Expr[] k = merge_products(R_p, q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = p_1;
	    if(k.length < R_p.length + q.length)
		return simplify_product_rec(tmp);
	    return tmp;
	}
	else
	{
	    Expr[] k = merge_products(p, R_q);
	    Expr[] tmp = new Expr[k.length + 1];
	    for(int i = 1; i < tmp.length; i++)
		tmp[i] = k[i - 1];
	    tmp[0] = q_1;
	    if(k.length < R_p.length + q.length)
		return simplify_product_rec(tmp);
	    return tmp;
	}
    }

    public static Expr simplify_power(Expr u)
    {
	Expr[] vw = base_exp(u);
	Expr v = vw[0];
	Expr w = vw[1];
	if(v.equals(Constant.UNDEFINED) || w.equals(Constant.UNDEFINED))
	    return Constant.UNDEFINED;

	if(v.equals(Int.ZERO) && w instanceof Numerical)
	{
	    if(((Numerical) w).compareTo(Int.ZERO) == 1)
		return Int.ZERO;
	    else
		return Constant.UNDEFINED;
	}

	if(v.equals(Int.ONE))
	    return Int.ONE;

	if(v.equals(Constant.E))
	    return new Expr(Operator.EXP, w);

	if(w instanceof Int)
	    return simplify_integer_pow(v, (Int) w);

	if(w instanceof Rational
		&& v instanceof Numerical)
	    return simplify_num_fraction_power((Numerical) v, (Rational) w);

	if(v.isProduct() && is_positive(v.get(0)))
	{
	    Expr s = simplify_power(new Expr(Operator.POWER, new Expr[] {v.get(0), w}));
	    Expr d = simplify_power(new Expr(Operator.POWER, new Expr[] {
		    simplify_product(new Expr(Operator.MULTIPLY, v.rest())), w}));
	    return simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {s, d}));
	}

	if(v.isPower())
	{
	    Expr vb = v.get(0);
	    Expr ve = v.get(1);
	    if(is_positive(vb))
	    {
		Expr p = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {ve, w}));
		return simplify_power(new Expr(Operator.POWER, new Expr[] {vb, p}));
	    }
	}
	if(w.isSum() && v.isNumerical())
	{
	    Expr F = w.get(0);
	    if(F.isInt())
	    {
		Expr S_1 = simplify_power(new Expr(Operator.POWER, new Expr[] {v, w.sub(F)}));
		Expr S_2 = simplify_power(new Expr(Operator.POWER, new Expr[] {v, F}));
		Expr P = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {S_1, S_2}));
		return P;
	    }
	}

	return u;
    }

    private static Expr simplify_num_fraction_power(Numerical v, Rational w)
    {
	if(v.compareTo(Int.ZERO) == -1 && w.equals(new Rational(Int.ONE, Int.TWO)))
	{
	    Expr P = simplify_power(new Expr(Operator.POWER, new Expr[] {v.mul(Int.NONE), w}));
	    return Simplification.simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {P,
		    Constant.I}));
	}
	if(v instanceof Int && v.compareTo(Int.ZERO) == 1 && w.compareTo(Int.ZERO) == 1)
	    return simplify_Int_fraction_power((Int) v, w);
	if(v instanceof Rational && v.compareTo(Int.ZERO) == 1)
	    return simplify_fraction_fraction_power((Rational) v, w);
	if(v instanceof Int && w.compareTo(Int.ZERO) == -1)
	    return simplify_fraction_fraction_power(new Rational((Int) v, Int.ONE), w);

	return new Expr(Operator.POWER, new Expr[] {v, w});
    }

    private static Expr simplify_fraction_fraction_power(Rational v, Rational w)
    {
	if(w.compareTo(Int.ZERO) == -1)
	{
	    Numerical a = v.inverse().make_normal();
	    if(a instanceof Int)
		return simplify_Int_fraction_power((Int) a, w.mul(Int.NONE));
	    v = (Rational) a;
	    w = w.mul(Int.NONE);
	}
	// Now we are sure that w is positive
	Int k = w.getNumerator().divide(w.getDenominator());
	Numerical c = (Numerical) v.pow(k);
	Rational rest = w.sub(k);
	Rational pow = (Rational) Int.ONE.sub(rest);
	Int n = v.getDenominator();
	Expr m = simplify_power(new Expr(Operator.POWER, new Expr[] {v.getNumerator(), rest}));
	Expr n_u = simplify_power(new Expr(Operator.POWER, new Expr[] {n, pow}));
	return simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {m, n_u,
		new Rational(Int.ONE, n), c}));
    }

    private static Expr simplify_Int_fraction_power(Int v, Rational w)
    {
	Int k = w.getNumerator().divide(w.getDenominator());
	Int c = (Int) v.pow(k);
	Rational rest = w.sub(k);
	Int[][] fac = v.square_free_factor();
	if(fac.length == 1)
	{
	    Numerical pow = fac[0][1].mul(rest);
	    if(pow instanceof Int)
	    {
		if(c.equals(Int.ONE))
		    return simplify_integer_pow(fac[0][0], (Int) pow);
		return simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {
			simplify_integer_pow(fac[0][0], (Int) pow), c}));
	    }
	    else
	    {
		if(fac[0][1].equals(Int.ONE))
		{
		    if(c.equals(Int.ONE))
			return new Expr(Operator.POWER, new Expr[] {fac[0][0], pow});
		    return simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {
			    new Expr(Operator.POWER, new Expr[] {fac[0][0], pow}), c}));
		}
		else
		{
		    if(c.equals(Int.ONE))
			return simplify_Int_fraction_power(fac[0][0], (Rational) pow);
		    return simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {
			    simplify_Int_fraction_power(fac[0][0], (Rational) pow), c}));
		}
	    }
	}
	Expr[] prod;
	if(c.equals(Int.ONE))
	    prod = new Expr[fac.length];
	else
	    prod = new Expr[fac.length + 1];
	for(int i = 0; i < fac.length; i++)
	{
	    prod[i] = simplify_power(new Expr(Operator.POWER, new Expr[] {fac[i][0],
		    fac[i][1].mul(rest)}));
	}
	if(!c.equals(Int.ONE))
	    prod[prod.length - 1] = c;
	return simplify_product(new Expr(Operator.MULTIPLY, prod));
    }

    private static Expr simplify_integer_pow(Expr v, Int n)
    {
	if(v instanceof Numerical)
	    return ((Numerical) v).pow(n);

	if(v.isMatrix())
	{
	    try
	    {
		return new Expr(Operator.MATRIX, Set.toList(Matrix.power(Set.toExprArray(v.get(0)),
			n)));
	    }
	    catch(SingularMatrixException e)
	    {
		InOut.parser_output("[Simplification] Warning: Matrix is singular");
		return Constant.UNDEFINED;
	    }
	}
	if(v.getOperator().equals(Operator.PSERIES))
	{
	    Series c = new Series(v.get(0).getOperands()).pow(n);
	    return new Expr(Operator.PSERIES, new Expr(Operator.LIST, c.getCoefs()), v.get(1));
	}
	if(n.equals(Int.ZERO))
	    return Int.ONE;

	if(n.equals(Int.ONE))
	    return v;

	if(v.equals(Constant.I))
	{
	    return simplify_imaginary_pow(n);
	}

	Numerical[] gr = gaussian_rational(v);
	if(gr != null)
	{
	    return simplify_gr_pow(gr, n);
	}

	if(v instanceof ModIntSym)
	{
	    return ((ModIntSym) v).power(n);
	}
	if(v instanceof ModIntNon)
	{
	    return ((ModIntNon) v).power(n);
	}
	if(v.getOperator().equals(Operator.POWER))
	{
	    Expr r = v.get(0);
	    Expr s = v.get(1);
	    Expr p = simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {s, n}));

	    if(p instanceof Int)
		return simplify_integer_pow(r, (Int) p);
	    else
		return simplify_power(new Expr(Operator.POWER, new Expr[] {r, p}));
	}
	if(v.getOperator().equals(Operator.MULTIPLY))
	{
	    Expr[] tmp = new Expr[v.length()];
	    for(int i = 0; i < tmp.length; i++)
		tmp[i] = simplify_integer_pow(v.get(i), n);
	    Expr r = new Expr(Operator.MULTIPLY, tmp);
	    return simplify_product(r);
	}

	return new Expr(Operator.POWER, new Expr[] {v, n});
    }

    private static Expr simplify_gr_pow(Numerical[] gr, Int n)
    {
	if(n.compareTo(Int.ZERO) >= 0)
	{
	    Numerical[] j = Numerical.pow(gr, n);
	    Expr P = Simplification.simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {j[1],
		    Constant.I}));
	    Expr S = Simplification.simplify_sum(new Expr(Operator.ADD, new Expr[] {j[0], P}));
	    return S;
	}
	else
	{
	    n = n.mul(Int.NONE);
	    Numerical[] j = Numerical
		    .div(new Numerical[] {Int.ONE, Int.ZERO}, Numerical.pow(gr, n));
	    Expr P = Simplification.simplify_product(new Expr(Operator.MULTIPLY, new Expr[] {j[1],
		    Constant.I}));
	    Expr S = Simplification.simplify_sum(new Expr(Operator.ADD, new Expr[] {j[0], P}));
	    return S;
	}
    }

    public static Numerical[] gaussian_rational(Expr v)
    {
	if(v.equals(Int.ZERO))
	    return new Numerical[] {Int.ZERO, Int.ZERO};
	if(v.isNumerical())
	    return new Numerical[] {(Numerical) v, Int.ZERO};
	if(v.equals(Constant.I))
	    return new Numerical[] {Int.ZERO, Int.ONE};
	if(v.isProduct() && v.length() == 2)
	{
	    Expr A = v.get(0);
	    Expr B = v.get(1);
	    if(A.isNumerical() && B.equals(Constant.I))
		return new Numerical[] {Int.ZERO, (Numerical) A};
	}
	if(v.isSum() && v.length() == 2)
	{
	    Expr A = v.get(0);
	    Expr B = v.get(1);
	    if(A.isNumerical() && B.equals(Constant.I))
		return new Numerical[] {(Numerical) A, Int.ONE};
	    if(A.isNumerical() && B.isProduct() && B.length() == 2)
	    {
		Expr B_1 = B.get(0);
		Expr B_2 = B.get(1);
		if(B_1.isNumerical() && B_2.equals(Constant.I))
		    return new Numerical[] {(Numerical) A, (Numerical) B_1};
	    }
	}
	return null;
    }

    private static Expr simplify_imaginary_pow(Int n)
    {
	if(n.compareTo(Int.ZERO) >= 0)
	{
	    Int k = n.mod(new Int("4"));
	    if(k.equals(Int.ZERO))
		return Int.ONE;
	    if(k.equals(Int.ONE))
		return Constant.I;
	    if(k.equals(Int.TWO))
		return Int.NONE;
	    if(k.equals(new Int("3")))
		return new Expr(Operator.MULTIPLY, new Expr[] {Int.NONE, Constant.I});
	}
	else
	{
	    Int k = n.mul(Int.NONE).mod(new Int("4"));
	    if(k.equals(Int.ZERO))
		return Int.ONE;
	    if(k.equals(Int.ONE))
		return new Expr(Operator.MULTIPLY, new Expr[] {Int.NONE, Constant.I});
	    if(k.equals(Int.TWO))
		return Int.NONE;
	    if(k.equals(new Int("3")))
		return Constant.I;
	}
	return null;
    }

    public static Expr simplify_rational_int_powers_in_product(Expr[] p)
    {
	if(p.length == 1)
	    return new Expr(Operator.MULTIPLY, p);
	Vector<Expr> pr = new Vector<Expr>();
	Vector<Int> ints = new Vector<Int>();
	Vector<Expr> exponents = new Vector<Expr>();
	boolean combined = false;
	for(int i = 0; i < p.length; i++)
	{
	    Expr[] be = base_exp(p[i]);
	    if(be[0].isNaturalNumber())
	    {
		boolean add = true;
		for(int j = 0; j < exponents.size(); j++)
		{
		    if(exponents.get(j).equals(be[1]))
		    {
			ints.setElementAt(ints.get(j).mul((Int) be[0]), j);
			add = false;
			combined = true;
		    }
		}
		if(add)
		{
		    ints.add((Int) be[0]);
		    exponents.add(be[1]);
		}
	    }
	    else
	    {
		pr.add(p[i]);
	    }
	}
	if(!combined)
	    return new Expr(Operator.MULTIPLY, p);
	for(int i = 0; i < ints.size(); i++)
	    pr.add(ints.get(i).pow(exponents.get(i)));
	return new Expr(Operator.MULTIPLY, pr.toArray(new Expr[pr.size()]));
    }

    public static boolean is_positive(Expr u)
    {
	if(u.isNumerical())
	    return ((Numerical) u).compareTo(Int.ZERO) > 0;
	if(u.equals(Constant.PI))
	    return true;
	if(u.equals(Constant.E))
	    return true;
	if(u.equals(Constant.I))
	    return false;
	if(u.isSum())
	{
	    for(int i = 0; i < u.length(); i++)
		if(!is_positive(u.get(i)))
		    return false;
	    return true;
	}
	if(u.isProduct())
	{
	    int sign = 1;
	    for(int i = 0; i < u.length(); i++)
	    {
		if(is_positive(u.get(i)))
		    sign = 1 * sign;
		else
		{
		    if(is_negative(u.get(i)))
			sign = -1 * sign;
		    else
			return false;
		}
	    }
	    if(sign > 0)
		return true;
	    if(sign < 0)
		return false;
	}
	if(u.isPower())
	{
	    return is_positive(u.get(0)) && is_real(u.get(1));
	}

	if(u.getOperator().equals(Operator.EXP))
	    return is_real(u.get(0));
	if(u.getOperator().equals(Operator.LOG))
	    return is_positive(u.get(0).sub(Int.ONE));
	if(u.getOperator().equals(Operator.ARCTAN))
	    return is_positive(u.get(0));

	return false;
    }

    public static boolean is_negative(Expr u)
    {
	if(u.isNumerical())
	    return ((Numerical) u).compareTo(Int.ZERO) < 0;
	if(u.equals(Constant.PI))
	    return false;
	if(u.equals(Constant.E))
	    return false;
	if(u.equals(Constant.I))
	    return false;
	if(u.isSum())
	{
	    for(int i = 0; i < u.length(); i++)
		if(!is_negative(u.get(i)))
		    return false;
	    return true;
	}
	if(u.isProduct())
	{
	    int sign = 1;
	    for(int i = 0; i < u.length(); i++)
	    {
		if(is_positive(u.get(i)))
		    sign = 1 * sign;
		else
		{
		    if(is_negative(u.get(i)))
			sign = -1 * sign;
		    else
			return false;
		}
	    }
	    if(sign < 0)
		return true;
	    if(sign > 0)
		return false;
	}
	if(u.isPower())
	{
	    return false;
	}

	if(u.getOperator().equals(Operator.LOG))
	    return is_positive(Int.ONE.sub(u.get(0)));
	if(u.getOperator().equals(Operator.ARCTAN))
	    return is_negative(u.get(0));
	return false;
    }

    public static boolean is_real(Expr u)
    {
	if(u.isNumerical())
	    return true;
	if(u.equals(Constant.PI))
	    return true;
	if(u.equals(Constant.E))
	    return true;
	if(u.equals(Constant.I))
	    return false;

	if(u.isProduct() || u.isSum())
	{
	    for(int i = 0; i < u.length(); i++)
		if(!is_real(u.get(i)))
		    return false;
	    return true;
	}
	if(u.isPower())
	{
	    Expr A = u.get(0);
	    Expr B = u.get(1);
	    if(is_real(A) && B.isInt())
		return true;
	    if(is_positive(A) && is_real(B))
		return true;
	    return false;
	}
	Operator P = u.getOperator();
	if(P.equals(Operator.EXP))
	    return is_real(u.get(0));

	if(P.equals(Operator.LOG))
	    return is_positive(u.get(0));
	return false;
    }

    public static Expr[] merge_sort(Expr[] expr)
    {
	if(expr.length <= 1)
	    return expr;
	int n = expr.length / 2;
	Expr[] left = new Expr[n];
	Expr[] right = new Expr[expr.length - n];
	for(int i = 0; i < n; i++)
	    left[i] = expr[i];
	for(int i = 0; i < right.length; i++)
	    right[i] = expr[i + n];
	return merge(merge_sort(left), merge_sort(right));
    }

    private static Expr[] merge(Expr[] l, Expr[] r)
    {
	Expr[] nl = new Expr[l.length + r.length];
	int l_i = 0;
	int r_i = 0;
	int nl_i = 0;
	while(l_i < l.length && r_i < r.length)
	{
	    if(Expr.compare(l[l_i], r[r_i]) >= 0)
	    {
		nl[nl_i] = l[l_i];
		nl_i++;
		l_i++;
	    }
	    else
	    {
		nl[nl_i] = r[r_i];
		nl_i++;
		r_i++;
	    }
	}
	while(l_i < l.length)
	{
	    nl[nl_i] = l[l_i];
	    nl_i++;
	    l_i++;
	}
	while(r_i < r.length)
	{
	    nl[nl_i] = r[r_i];
	    nl_i++;
	    r_i++;
	}
	return nl;
    }

    public static Expr[] constant_term(Expr e)
    {
	if(e.isProduct())
	{
	    Numerical n = Int.ONE;
	    Vector<Expr> v = new Vector<>();
	    for(int i = 0; i < e.length(); i++)
	    {
		if(e.get(i).isNumerical())
		    n = n.mul((Numerical) e.get(i));
		else
		    v.add(e.get(i));
	    }
	    if(v.size() > 1)
		return new Expr[] {n, new Expr(Operator.MULTIPLY, v.toArray(new Expr[v.size()]))};
	    if(v.size() == 1)
		return new Expr[] {n, v.get(0)};
	    return new Expr[] {n, Int.ONE};
	}
	return new Expr[] {Int.ONE, e};
    }

    public static Expr[] constant_mod_term(Expr e)
    {
	if(e.isProduct())
	{
	    Expr n = Int.ONE;
	    Vector<Expr> v = new Vector<>();
	    for(int i = 0; i < e.length(); i++)
	    {
		if(e.get(i).isNumerical() || e.get(i) instanceof ModIntSym
			|| e.get(i) instanceof ModIntNon)
		    n = n.mul(e.get(i));
		else
		    v.add(e.get(i));
	    }
	    if(v.size() > 1)
		return new Expr[] {n, new Expr(Operator.MULTIPLY, v.toArray(new Expr[v.size()]))};
	    if(v.size() == 1)
		return new Expr[] {n, v.get(0)};
	    return new Expr[] {n, Int.ONE};
	}
	return new Expr[] {Int.ONE, e};
    }

    public static Expr[] constant_term(Expr e, Expr... x)
    {
	if(e.isProduct())
	{
	    Expr n = Int.ONE;
	    Expr v = Int.ONE;
	    for(int i = 0; i < e.length(); i++)
	    {
		if(e.get(i).isFreeOf(x))
		    n = n.mul(e.get(i));
		else
		    v = v.mul(e.get(i));
	    }

	    return new Expr[] {n, v};
	}
	return constant_term(new Expr(Operator.MULTIPLY, e), x);
    }

    public static Expr[] base_exp(Expr e)
    {
	if(e instanceof Numerical)
	    return new Expr[] {Constant.UNDEFINED, Constant.UNDEFINED};
	if(e.isPower())
	{
	    return new Expr[] {e.get(0), e.get(1)};
	}
	return new Expr[] {e, Int.ONE};
    }

    public static Expr[] getList(Expr b)
    {
	if(b.getOperator().equals(Operator.LIST))
	{
	    Expr[] q = new Expr[b.length()];
	    for(int i = 0; i < q.length; i++)
		q[i] = b.get(i);
	    return q;
	}
	return new Expr[] {b};
    }

    public static boolean isListOf(Expr[] b, Class<?> c)
    {
	for(int i = 0; i < b.length; i++)
	    if(!(b[i].getClass().equals(c)))
		return false;
	return true;
    }

    public static Int[] castToInt(Expr[] e)
    {
	Int[] j = new Int[e.length];
	for(int i = 0; i < e.length; i++)
	    j[i] = (Int) e[i];
	return j;
    }

    public static Expr[] getNewVariables(int n, Expr... e)
    {
	Expr[] s = new Expr[n];
	int j = 0;
	for(int i = 0; i < n; i++)
	{
	    Var v = new Var("&" + j);
	    while(!Expr.isFreeOf(e, v))
	    {
		j++;
		v = new Var("&" + j);
	    }
	    s[i] = v;
	    j++;
	}
	return s;
    }

    public static Expr expand_product(Expr[] u)
    {
	return Algebra.expand(simplify_recursive(new Expr(Operator.MULTIPLY, u)));
    }

    public static Expr simplify_power_fraction(Expr u, Expr x)
    {
	if(u.isSymbolic())
	    return u;
	Expr[] v = new Expr[u.length()];
	for(int i = 0; i < v.length; i++)
	    v[i] = simplify_power_fraction(u.get(i), x);
	Expr U = simplify_recursive(new Expr(u.getOperator(), v));
	if(U.isPower())
	{
	    Expr b = U.get(0);
	    Expr e = U.get(1);
	    if(b.isPower())
	    {
		Expr c = b.get(0);
		Expr h = b.get(1);
		if(c.equals(x))
		    return x.pow(h.mul(e));
	    }
	}
	return U;
    }

    public static boolean isZero(Expr p)
    {
	return Algebra.cancel(p).equals(Int.ZERO);
    }
}
