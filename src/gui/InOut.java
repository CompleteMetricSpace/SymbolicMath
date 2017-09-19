package gui;

import java.util.Vector;

import Expression.Expr;
import Expression.Operator;
import Expression.Parser;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;
import Symbolic.Symbolic;
import Symbolic.Var;

public class InOut
{
    public static Vector<Var> variables = new Vector<>();
    public static Vector<Expr> values = new Vector<>();
    public static Vector<String> input = new Vector<>();
    public static Vector<Expr> output = new Vector<>();
    public static Out out;
    
    public static interface Out
    {
	public void parser_output(String s);
	public void program_output(String s);
    }

    public static String out(String in)
    {
	return out(in, false);
    }
    
    public static String out(String in, boolean numeric)
    {
	String[] s = out_split(in, numeric);
	return s[0]+s[1];
    }
    
    public static String[] out_split(String in, boolean numeric)
    {
	boolean no_output = false;
	in = in.trim();
	if(in.isEmpty())
	{
	    return new String[]{"",""};
	}
	if(in.equals("\\clear"))
	{
	    return new String[]{"~CLEAR_PARSER_IO~",""};
	}
	String[] cd = split(in, ";");
	System.out.println("cd: "+cd.length);
	if(cd.length > 1)
	{
	    for(int i = 0; i < cd.length - 1; i++)
		out(cd[i], numeric);
	    return out_split(cd[cd.length - 1], numeric);
	}
	try
	{
	    int assign = in.indexOf(":=");
	    Expr out;
	    if(assign != -1)
	    {
		String v = in.substring(0, assign);
		String e = in.substring(assign + 2, in.length());
		Expr var = Parser.parse(v);
		Expr expr = Parser.parse(e);
		if(!var.isVar())
		    return new String[]{"Assignment Error: <" + var + "> is not a variable", ""};
		Expr s = substitute(expr);
		s = Simplification.simplify_recursive(s);
		set_value((Var) var, s);
		out = s;
	    } else
	    {
		if(in.startsWith("delete"))
		{
		    String v = in.substring(6);
		    v = v.trim();
		    if(v.isEmpty())
			return new String[]{"Delete Error: no variables given to delete", ""};
		    Expr[] es = Parser.parseArgs(v);
		    for(int i = 0; i < es.length; i++)
		    {
			if(!es[i].isVar())
			    return new String[]{"Assignment Error: <" + es[i] + "> is not a variable", ""};
			else
			    delete_value((Var) es[i]);
		    }
		    out = Constant.VOID;
		} else
		{
		    if(numeric)
			in = "N("+in+",12)";
		    Expr expr = Parser.parse(in);
		    expr = substitute(expr);
		    expr = Simplification.simplify_recursive(expr);
		    out = expr;
		}
	    }
	    input.add(in);
	    output.add(out);
	    if(no_output)
		return new String[]{"",""};
	    return new String[]{"Out(" + output.size() + ") -> " , out.toStringUniCode()};
	} catch(Exception e)
	{
	    e.printStackTrace();
	    return new String[]{e.toString(),""};
	}
    }

    public static void set_value(Var a, Expr b)
    {
	boolean has = false;
	for(int i = 0; i < variables.size(); i++)
	{
	    if(variables.get(i).equals(a))
	    {
		values.set(i, b);
		has = true;
	    }
	}
	if(!has)
	{
	    variables.add(a);
	    values.add(b);
	}
    }

    public static void delete_value(Var a)
    {
	for(int i = 0; i < variables.size(); i++)
	{
	    if(variables.get(i).equals(a))
	    {
		variables.remove(i);
		values.remove(i);
		break;
	    }
	}
    }

    public static Expr substitute(Expr e)
    {
	for(int i = 0; i < variables.size(); i++)
	{
	    if(e.equals(variables.get(i)))
		return values.get(i);
	}
	if(e instanceof Symbolic)
	    return e;

	if(e.getOperator().equals(Operator.OUTPUT))
	{
	    if(e.get(0).isInt())
	    {
		int j = ((Int) e.get(0)).toInt() - 1;
		if(j >= 0 && j < output.size())
		    return output.get(j);
	    }
	}
	Expr[] d = new Expr[e.length()];
	for(int i = 0; i < e.length(); i++)
	    d[i] = substitute(e.get(i));
	return new Expr(e.getOperator(), d);
    }

    public static void program_output(String s)
    {
	if(out != null)
	    out.program_output(s);
    }

    public static void parser_output(String s)
    {
	if(out != null)
	    out.parser_output(s);
    }
    
    private static String[] split(String k, String s)
    {
	if(!k.endsWith(";"))
	    return k.split(s);
	else
	{
	    String[] h = k.split(s);
	    String[] g = new String[h.length+1];
	    for(int i = 0;i<h.length;i++)
	        g[i] = h[i];
	    g[g.length-1] = "";
	    return g;
	}
    }
}
