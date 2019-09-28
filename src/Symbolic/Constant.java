package Symbolic;

import Expression.Operator;

public class Constant extends Var
{

	
	public static Constant TRUE = new Constant("true");
	public static Constant FALSE = new Constant("false");
	public static Constant VOID = new Constant("void");
	public static Constant UNDEFINED = new Constant("undef");
	public static Constant FAIL = new Constant("fail");
	
	public static Constant I = new Constant("%i");
	public static Constant PI = new Constant("%pi");
	public static Constant E = new Constant("%e");
	
	public static Constant MODULAR = new Constant("modular");
	public static Constant EUCLID = new Constant("euclid");
	public static Constant SUBRESULTANT = new Constant("subresultant");
	
	public static Constant LEXOGRAPHIC = new Constant("lex");
	public static Constant REVGRADLEX = new Constant("revgradlex");
	public static Constant GRADLEX = new Constant("gradlex");
	
	public static Constant POS_INF = new Constant("%inf");
	public static Constant NEG_INF = new Constant("-%inf");
	
	public Constant(String name)
	{
		super(name);
	}

	public String toString() 
	{
		return name;
	}
}
