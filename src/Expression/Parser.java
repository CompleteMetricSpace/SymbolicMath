package Expression;
import java.math.BigDecimal;

import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Decimal;
import Symbolic.Greedy;
import Symbolic.Int;
import Symbolic.Literal;
import Symbolic.Mobile;
import Symbolic.ModIntNon;
import Symbolic.ModIntSym;
import Symbolic.Num;
import Symbolic.Rational;
import Symbolic.Str;
import Symbolic.Var;
import Symbolic.Wild;


public class Parser 
{

	
	public static Expr build(String s)
	{
		return Simplification.simplify_recursive(parse(s));
	}
	
	public static Expr build(String s, String[] v, Expr[] w)
	{
		Expr[] V = new Expr[v.length];
		for(int i = 0;i<v.length;i++)
			V[i] = new Var(v[i]);
		Expr d = parse(s);
		return Simplification.simplify_recursive(d.substitute(V, w));
	}
	
	public static boolean isInBrackets(String s, int index)
	{
		int b = 0;
		int c = 0;
		int d = 0;
		int i;
		for(i = 0;i<s.length();i++)
		{
			if(s.charAt(i) == '(')
				b++;
			if(s.charAt(i) == ')')
				b--;
			if(s.charAt(i) == '{')
				c++;
			if(s.charAt(i) == '}')
				c--;
			if(s.charAt(i) == '"')
			{
			    if(d == 1)
			    	d--;
			    else
			    	d++;
			}
			
			if(i == index)
			{
				break;
			}
		}
		if(b == 0 && c==0 && d == 0)
			return false;
		else
			return true;
	}
	
	public static int find_index_of(String s, String f)
	{
		int index = s.indexOf(f);
		while(index != -1 && isInBrackets(s, index))
			index = s.indexOf(f, index+1);
		return index;
	}
	
	public static int find_last_index_of(String s, String f)
	{
		int index = s.lastIndexOf(f);
		while(index != -1 && isInBrackets(s, index))
			index = s.lastIndexOf(f, index-1);
		return index;
	}
	
	public static Expr parse(String s)
	{
		s = s.trim();
		
		//Syntactic Sugar
		
		int index = find_index_of(s, "or ");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+3, s.length());
			return new Expr(Operator.OR, parse(a), parse(b));
		}
		
		index = find_index_of(s, "and ");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+4, s.length());
			return new Expr(Operator.AND, parse(a), parse(b));
		}
		
		index = find_index_of(s, "==");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+2, s.length());
			return new Expr(Operator.STRUCTURE_EQUALITY, parse(a), parse(b));
		}
		
		index = find_index_of(s, "=<");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+2, s.length());
			return new Expr(Operator.SMALLER_EQUAL, parse(a), parse(b));
		}
		
		index = find_index_of(s, ">=");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+2, s.length());
			return new Expr(Operator.BIGGER_EQUAL, parse(a), parse(b));
		}
		
		index = find_index_of(s, "<");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			return new Expr(Operator.SMALLER, parse(a), parse(b));
		}
		
		index = find_index_of(s, ">");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			return new Expr(Operator.BIGGER, parse(a), parse(b));
		}
		
		
		
		index = find_index_of(s, "=");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			return new Expr(Operator.EQUAL, parse(a), parse(b));
		}
		
		
		
	    index = find_index_of(s, "+");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			if(a.isEmpty())
				return parse(b);
			else
			    return new Expr(Operator.ADD, parse(a), parse(b));
		}
		
		index = find_last_index_of(s, "-");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			
			if(a.isEmpty())
				return new Expr(Operator.MULTIPLY, Int.NONE, parse(b));
			else
			{
				if(!isOperator(a.charAt(a.length()-1)))
				    return new Expr(Operator.ADD, parse(a), new Expr(Operator.MULTIPLY, Int.NONE, parse(b)));
			}
		}
		
		index = find_index_of(s, "*");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			return new Expr(Operator.MULTIPLY, parse(a), parse(b));
		}
		
		index = find_index_of(s, "\u2219");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			return new Expr(Operator.MULTIPLY, parse(a), parse(b));
		}
		
		index = find_last_index_of(s, "/");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			return new Expr(Operator.MULTIPLY, parse(a), new Expr(Operator.POWER, parse(b), Int.NONE));
		}
		
		index = find_index_of(s, "^");
		if(index != -1)
		{
			String a = s.substring(0, index);
			String b = s.substring(index+1, s.length());
			return new Expr(Operator.POWER, parse(a), parse(b));
		}

		if(s.charAt(0) == '(' && s.charAt(s.length()-1) == ')')
			return parse(s.substring(1, s.length()-1));
		
		if(s.charAt(0) == '{' && s.charAt(s.length()-1) == '}')
		{
			String l = s.substring(1, s.length()-1);
			l = l.trim();
			if(l.isEmpty())
				return new Expr(Operator.LIST);
			return new Expr(Operator.LIST, parseArgs(s.substring(1, s.length()-1)));
		}
		
		if(s.length()>2 && s.charAt(0) == 's' && s.charAt(1) == '{' && s.charAt(s.length()-1) == '}')
		{
			String l = s.substring(2, s.length()-1);
			l = l.trim();
			if(l.isEmpty())
				return new Expr(Operator.SET, new Expr(Operator.LIST)); //Empty set
			int h = find_index_of(l, "|");
			if(h != -1)
			{
				String a = l.substring(0, h);
				String b = l.substring(h+1, l.length());
				return new Expr(Operator.SET, Parser.parse(a), Parser.parse(b));
			}
			else
				return new Expr(Operator.SET, new Expr(Operator.LIST, parseArgs(l)));
		}
		
		if(s.length()>2 && s.charAt(0) == 'm' && s.charAt(1) == '{' && s.charAt(s.length()-1) == '}')
		{
			String l = s.substring(2, s.length()-1);
			return new Expr(Operator.MATRIX, new Expr(Operator.LIST, parseArgs(l)));
		}
		
		if(s.charAt(0) == '"' && s.charAt(s.length()-1) == '"')
		{
			return new Str(s.substring(1, s.length()-1));
		}
		
		for(int i = 0;i<Operator.operators.length;i++)
		{
			Operator op = Operator.operators[i];
			String op_name = op.getName();
			if(s.length() > op_name.length() && s.substring(0, op_name.length()+1).equals(op_name+"("))
			{
				String args = s.substring(op_name.length()+1, s.length()-1);
				Expr[] arguments = parseArgs(args);
				if(op.isRightOperandLength(arguments.length))
				{
					return new Expr(op, arguments);
				}
				else
				{
				    throw new WrongNumberOfArgumentsException(op_name, arguments.length);
				}
			}
		}
		if(s.length() > 8 && s.substring(0, 8).equals("Rational"))
		{
			String args = s.substring(9, s.length()-1);
			Expr[] arguments = parseArgs(args);
			if(arguments.length != 2)
			    throw new WrongNumberOfArgumentsException("Rational", arguments.length);
			return new Rational((Int)arguments[0], (Int)arguments[1]);
		}
		if(s.length() > 4 && s.substring(0, 4).equals("sqrt"))
		{
			String args = s.substring(5, s.length()-1);
			Expr arg = parse(args);
			return new Expr(Operator.POWER, arg, new Rational("1", "2"));
		}
		if(s.endsWith("!"))
		{
			Expr a = parse(s.substring(0, s.length()-1));
			return new Expr(Operator.FACTORIAL, a);
		}
		try
		{
			return new Int(s);
		}
		catch(NumberFormatException e){};
		int indexDot = s.indexOf('.');
		if(indexDot != -1)
		{
			try
			{
			    BigDecimal c = new BigDecimal(s);
			    return new Decimal(c);
			}
			catch(NumberFormatException e){};
		}
		if(s.startsWith("#"))
		{
			Expr e = parse(s.substring(1, s.length()));
			return new Mobile(s, e);
		}
		if(s.charAt(0) == '_')
		{
			if(s.charAt(1) == '&')
			    return new Literal(s);
			if(s.charAt(1) == 'n')
			    return new Num(s);
			if(s.charAt(1) == '_')
			    return new Greedy(s);
			
			return new Wild(s);
		}
		if(s.indexOf('(') != -1)
		{
			//Function?
			int n = s.indexOf('(');
			String name = s.substring(0, n);
			int i = 0; String prime = "'";
			while(name.endsWith(prime)){i++; prime += "'";}
			Expr[] args = parseArgs(s.substring(n+1, s.length()-1));
			name = name.substring(0, name.length()-i);
			Operator op = new Operator(name, name, "function", false, args.length);
			if(i == 0)
			    return new Expr(op, args);
			if(args.length != 1)
				throw new IllegalArgumentException("Prime ' only allowed on functions in one variable");
			return new Expr(Operator.FDERIV, op, new Int(i), args[0]);
		}
		
		if(s.equals("true"))
		    return Constant.TRUE;
		if(s.equals("false"))
		    return Constant.FALSE;
		if(s.equals("%i"))
	            return Constant.I;
		if(s.equals("%e"))
			return Constant.E;
		if(s.equals("%pi"))
			return Constant.PI;
		if(s.equals("\u03c0"))
			return Constant.PI;
		if(s.equals("I"))
			return Constant.I;
		if(s.equals("E"))
			return Constant.E;
		if(s.equals("Pi"))
			return Constant.PI;
	    return new Var(s);
	}

	public static Expr[] parseArgs(String s) 
	{
		int indexComma = s.indexOf(",");
		while(isInBrackets(s, indexComma) && indexComma != -1)
			indexComma = s.indexOf(",", indexComma+1);
		if(indexComma == -1)
		    return new Expr[]{parse(s)};
		String g = s.substring(0, indexComma);
		String rest = s.substring(indexComma+1, s.length());
		Expr[] r = parseArgs(rest);
		Expr f = parse(g);
		Expr[] t = new Expr[r.length+1];
		t[0] = f;
		for(int i = 1;i<t.length;i++)
			t[i] = r[i-1];
		return t;
	}

	public static boolean isLetter(char c) 
	{
		if("abcdefghijklmnopqrtstuvxyzABCDEFGHIJKLMNOPQRSTUVWXYZ".indexOf(c) > 0)
			return true;
		return false;
	}

	public static boolean isOperator(char c) 
	{
		if("+-*/^".indexOf(c) > 0)
			return true;
		return false;
	}
	
}
