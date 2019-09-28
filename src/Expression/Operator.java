package Expression;

import Symbolic.Constant;

public class Operator extends Constant
{
    
	 String name;
     String symbol;
     String type;
     int[] operands;
     boolean commutative;
     
     public static Operator NULL = new Operator("null", "null", "no type", false, 0);
     public static Operator OUTPUT = new Operator("Out", "Out", "function", false, 1);
     
     public static Operator ADD = new Operator("add", "+", "operator", true, -1);
     public static Operator MULTIPLY = new Operator("multiply", "*", "operator", true, -1);
     public static Operator POWER = new Operator("power", "^", "operator",true, 2);
   
     public static Operator LIST = new Operator("list", "list", "function",false, -1);
     public static Operator ARGS = new Operator("args", "args", "function", false, -1);
     public static Operator CONTAINS = new Operator("contains", "contains", "function", false, 1);
     public static Operator HOLD = new Operator("hold", "hold", "function", false, 1);
     public static Operator RELEASE = new Operator("release", "release", "function", false, 1);
     public static Operator TIME = new Operator("time", "time", "function", false, 1);
     
     public static Operator BIG_O = new Operator("O", "O", "function", false, 2);
     
     public static Operator TO_STRING = new Operator("tostr", "tostr", "function", false, 1);
     public static Operator ADD_STRING = new Operator("addstr", "addstr", "function", false, -1);
     public static Operator TO_EXPR = new Operator("toexpr", "toexpr", "function", false, 1);
     public static Operator CHAR_AT = new Operator("charat", "charat", "function", false, 2);
     
     public static Operator SMALLER = new Operator("smaller", "<", "function", false, 2);
     public static Operator BIGGER = new Operator("bigger", ">", "function", false, 2);
     public static Operator BIGGER_EQUAL = new Operator("bigger_equal", ">=", "function", false, 2);
     public static Operator SMALLER_EQUAL = new Operator("smaller_equal", "=<", "function", false, 2);
     public static Operator EQUAL = new Operator("equal", "=", "function", true, 2);
     public static Operator STRUCTURE_EQUALITY = new Operator("same", "==", "function", true, 2);
    
     public static Operator MODULUS = new Operator("mod", "mod", "function", false, 2);
     public static Operator I_QUOTIENT = new Operator("iquot", "iquot", "function", false, 2);
     public static Operator INTEGER_GCD = new Operator("gcd", "gcd", "function", false, 1);
     public static Operator INTEGER_EXTENDED_GCD = new Operator("extgcd", "extgcd", "function", false, 1);
     public static Operator INTEGER_LCM = new Operator("lcm", "lcm", "function", false, 1); 
     public static Operator BINOMIAL = new Operator("binom", "binom", "function", false, 2);
     public static Operator FACTORIAL = new Operator("factorial", "factorial", "function", false, 1);
     public static Operator SYM_MOD_INT = new Operator("smodi", "smodi", "function", false, 2);
     public static Operator NN_MOD_INT = new Operator("nmodi", "nmodi", "function", false, 2);
     public static Operator PRIME_LIST = new Operator("primelist", "primelist", "function", false, 1);
     public static Operator IS_PRIME = new Operator("isprime", "isprime", "function", false, 1);
     public static Operator FACTOR_INTEGER = new Operator("ifactor", "ifactor", "function", false, 1);    
     public static Operator INTEGER_CHINESE_REMAINDER = new Operator("chineserem", "chineserem", "function", false, 1);
     
     public static Operator EXP = new Operator("exp", "exp", "function", false, 1);
     public static Operator LOG = new Operator("log", "log", "function", false, 1);
     public static Operator ARCTAN = new Operator("arctan", "arctan", "function", false, 1);
     public static Operator ARCSIN = new Operator("arcsin", "arcsin", "function", false, 1);
     public static Operator ARCCOS = new Operator("arccos", "arccos", "function", false, 1);
     public static Operator SIN = new Operator("sin", "sin", "function", false, 1);
     public static Operator COS = new Operator("cos", "cos", "function", false, 1);
     public static Operator TAN = new Operator("tan", "tan", "function", false, 1);
     public static Operator SINH = new Operator("sinh", "sinh", "function", false, 1);
     public static Operator COSH = new Operator("cosh", "cosh", "function", false, 1);
     
     public static Operator ABSOLUTE_VALUE = new Operator("abs", "abs", "function", false, 1);
     public static Operator SIGNUM = new Operator("sign", "sign", "function", false, 1);
     public static Operator MINIMUM = new Operator("min", "min", "function", false, 1);
     public static Operator MAXIMUM = new Operator("max", "max", "function", false, 1);
     
     public static Operator NOT = new Operator("not", "not", "function", false, 1);
     public static Operator OR = new Operator("opor", "or", "function", true, -1);
     public static Operator AND = new Operator("opand", "and", "function", true, -1);
     public static Operator EXISTS = new Operator("exists", "exists", "function", false, 3);
     public static Operator FORALL = new Operator("forall", "forall", "function", false, 3); 
     
     public static Operator EXPAND = new Operator("expand", "expand", "function", false, 1, 2);
     public static Operator COLLECT = new Operator("collect", "collect", "function", false, 2);
     public static Operator RATIONALIZE = new Operator("rational", "rational", "function", false, 1);
     public static Operator CANCEL = new Operator("cancel", "cancel", "function", false, 1);
     public static Operator POLY_COEF = new Operator("coefficient", "coefficient", "function", false, 3);
     public static Operator POLY_DEGREE = new Operator("degree", "degree", "function", false, 2); 
     public static Operator POLY_REMAINDER = new Operator("prem", "prem", "function", false, 3, 4); 
     public static Operator POLY_QUOTIENT = new Operator("pquot", "pquot", "function", false, 3, 4); 
     public static Operator SFFACTOR = new Operator("squarefree", "squarefree", "function", false, 3);
     public static Operator FACTOR_POLYNOMIAL = new Operator("factor", "factor", "function", false, 1, 2);
     public static Operator FACTOR_POLYNOMIAL_LIST = new Operator("factorlist", "factorlist", "function", false, 1, 2);
     public static Operator DECOMPOSE_POLYNOMIAL = new Operator("decompose", "decompose", "function", false, 2);
     public static Operator GROEBNER_BASIS = new Operator("gbasis", "gbasis", "function", false, 2);
     public static Operator POLYNOMIAL_GCD = new Operator("pgcd", "pgcd", "function", false, 1, 2);
     public static Operator RESULTANT = new Operator("resultant", "resultant", "functon", false, 3);
     public static Operator SUBRESULTANT = new Operator("subresultant", "subresultant", "function",false, 3);
     public static Operator POLYNOMIAL_EXTENDED_GCD = new Operator("pextgcd", "pextgcd", "function", false, 2);
     public static Operator SIMPLIFY_SIDE_RELATIONS = new Operator("psimplify", "psimplify", "function", false, 3);
     
     public static Operator MODULO = new Operator("modulo", "modulo", "function", false, 1);
     public static Operator ALGEBRAIC_EXTENSION = new Operator("extension", "extension", "function", false, 2);
     
     public static Operator CYCLOTOMIC_POLYNOMIAL = new Operator("cyclotomic", "cyclotomic", "function", false, 2);
     public static Operator SWINNERTON_DYER_POLYNOMIAL = new Operator("sdpoly", "sdpoly", "function", false, 2);
     
     public static Operator SIMPLIFY_RADICAL = new Operator("radsimp", "radsimp", "function", false, 1, 2);
     public static Operator CONTRACT = new Operator("contract", "contract", "function", false, 1, 2);
     public static Operator DENEST = new Operator("denest", "denest", "function", false, 1);
     public static Operator ISOLATE_ROOTS = new Operator("isolateroots", "isolateroots", "function", false, 2, 3);
     
     public static Operator OPERAND = new Operator("operand", "operand", "function", false, 2);
     public static Operator LENGTH = new Operator("length", "length", "function", false, 1);
     public static Operator KIND = new Operator("kind", "kind", "function", false, 1);
     public static Operator NUMERATOR = new Operator("numerator", "numerator", "function" ,false, 1);
     public static Operator DENOMINATOR = new Operator("denominator", "denominator", "function" ,false, 1);
     
     public static Operator SUBSTITUTE = new Operator("subst", "subst", "function", false, 3);
     public static Operator ADJOIN = new Operator("adjoin", "adjoin", "function", false, 2);
     public static Operator UNION = new Operator("union", "union", "function", false, -1);
     public static Operator INTERSECTION = new Operator("intersection", "intersection", "function", false, -1);
     public static Operator TABLE = new Operator("table", "table", "function", false, 4);
     
     public static Operator SET = new Operator("set", "set", "function", false, 1, 2);
     public static Operator MEMBER = new Operator("member", "member", "function", false, 2);
     
     public static Operator TOTAL_DIFFERENTIAL = new Operator("dt", "dt", "function", false, 1);     
     public static Operator DERIV = new Operator("deriv", "deriv", "function", false, 2, 3);     
     public static Operator FDERIV = new Operator("fderiv", "fderiv", "function", false, 3);
     public static Operator DIFFERENTIATE = new Operator("diff", "diff", "function", false, 1, 2);
     public static Operator LAPLACE_TRANSFORM = new Operator("laplace", "laplace", "function", false, 3);
     
     public static Operator DIFFERENCE_DELTA = new Operator("difference", "difference", "function", false, 2);
     
     public static Operator ROOTOF = new Operator("rootof", "rootof", "function", false, 3);
     
     public static Operator INTEGRATE_HEURISTIC = new Operator("int", "int", "function", false, 2);
     public static Operator INTEGRATE_RATIONAL = new Operator("ratint", "ratint", "function", false, 2);
     public static Operator GOSPER_SUMMATION = new Operator("gosper", "gosper", "function", false, 2, 4);
     public static Operator GOSPER_INTEGRATION = new Operator("hypint", "hypint", "function", false, 2);
     public static Operator RISCH_INTEGRATION = new Operator("risch", "risch", "function", false, 2);
     
     public static Operator NUMERICAL_EVAL = new Operator("N", "N", "function", false, 1, 2);
     
     public static Operator MATRIX = new Operator("matrix", "matrix", "function", false, 1);
     public static Operator DETERMINANT = new Operator("det", "det", "function", false, 1);
     public static Operator REDUCED_ROW_ECHELON = new Operator("rref", "rref", "function", false, 1);
     public static Operator TRANSPOSE = new Operator("transpose", "transpose", "function", false, 1);
     public static Operator COFACTOR_MATRIX = new Operator("cofactor", "cofactor", "function", false, 1);
     public static Operator IDENTITY_MATRIX = new Operator("identity", "identity", "function", false, 1);
     
     public static Operator PSERIES = new Operator("pseries", "pseries", "function", false, 2);
     public static Operator LAZYSERIES = new Operator("lzseries", "lzseries", "function", false, 3);
     
     public static Operator[] operators = {ADD, MULTIPLY, POWER, LIST, CONTAINS, SMALLER, BIGGER, SMALLER_EQUAL,
    	 BIGGER_EQUAL, EQUAL, STRUCTURE_EQUALITY, MODULUS, NOT, OR, AND, I_QUOTIENT, EXPAND, RATIONALIZE, POLY_COEF,
    	 OPERAND, LENGTH, KIND, ADJOIN, UNION, INTERSECTION, POLY_COEF, POLY_DEGREE, POLY_REMAINDER, POLY_QUOTIENT,
    	  INTEGER_GCD, SET, MEMBER, EXISTS, FORALL, OUTPUT, DERIV, FACTOR_POLYNOMIAL, FACTOR_POLYNOMIAL_LIST, 
    	  DECOMPOSE_POLYNOMIAL, ROOTOF, INTEGRATE_RATIONAL, DIFFERENTIATE, CANCEL, HOLD, RELEASE, TO_STRING, TO_EXPR,
    	  ADD_STRING, CHAR_AT, BIG_O, TIME, EXP, LOG, ABSOLUTE_VALUE, SIGNUM, MINIMUM, MAXIMUM, BINOMIAL, FACTORIAL,
    	  GOSPER_SUMMATION, SUBSTITUTE, DIFFERENCE_DELTA, GOSPER_INTEGRATION, RISCH_INTEGRATION, GROEBNER_BASIS, 
    	  SYM_MOD_INT, NN_MOD_INT, COLLECT, SIMPLIFY_RADICAL, CONTRACT, NUMERATOR, DENOMINATOR, INTEGER_LCM,
    	  INTEGER_EXTENDED_GCD, PRIME_LIST, POLYNOMIAL_GCD, RESULTANT, SUBRESULTANT, POLYNOMIAL_EXTENDED_GCD,
    	  CYCLOTOMIC_POLYNOMIAL, SWINNERTON_DYER_POLYNOMIAL, MODULO, ALGEBRAIC_EXTENSION, IS_PRIME, FACTOR_INTEGER, 
    	  INTEGRATE_HEURISTIC, TOTAL_DIFFERENTIAL, SIMPLIFY_SIDE_RELATIONS, NUMERICAL_EVAL, INTEGER_CHINESE_REMAINDER, 
    	  DENEST, ISOLATE_ROOTS, TABLE, MATRIX, DETERMINANT, REDUCED_ROW_ECHELON, TRANSPOSE, COFACTOR_MATRIX, IDENTITY_MATRIX,
    	  LAPLACE_TRANSFORM, PSERIES, LAZYSERIES
    	  };
     
     public Operator(String name, String symbol, String type, boolean com ,int... ops)
     {
    	 super(name);
    	 this.name = name;
    	 this.symbol = symbol;
    	 this.type = type;
    	 this.commutative = com;
    	 this.operands = ops;
     }
     
     public boolean equals(Operator b)
     {
    	 return name.equals(b.getName()) && b.isRightOperandLength(this.getArgsLength()[0]);
     }

	public String getName() 
	{
		return name;
	}
	
	public boolean isFunction()
	{
		return type.endsWith("function");
	}
	
	public boolean isCommutative()
	{
		return commutative;
	}
	
	public boolean isRightOperandLength(int k)
	{
		if(operands[0] == -1)
			return true;
		for(int i = 0;i<operands.length;i++)
		{
			if(operands[i] == k)
				return true;
		}
		return false;
	}
	
	public int[] getArgsLength()
	{
		return operands;
	}
	
	public static boolean hasOperator(Expr[] u, Operator op)
	{
		for(int i = 0;i<u.length;i++)
			if(u[i].getOperator().equals(op))
				return true;
		return false;
	}
}
