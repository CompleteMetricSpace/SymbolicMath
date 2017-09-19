package code;

import Symbolic.Var;

public class Programs 
{
	static String code_euclid_gcd = 
		    "while(not(same(b,0)))\n"
		   +"h:=prem(a,b,c);\n"
		   +"a:=b;\n"
		   +"b:=h;\n"
		   +"end;\n"
		   +"return a;\n";
	
	
	static Program euclid_gcd = new Program("euclid_gcd", to_code(code_euclid_gcd), new Var[]{new Var("a"), new Var("b")});
	
	
	public static Program[] prgms = new Program[]{euclid_gcd};
	
	public static String[] src_code = new String[]{code_euclid_gcd};
	
	public static Line[] to_code(String s)
	{
		try {
			return CodeParser.parse(s);
		}
		catch(Exception e)
		{
			
		}
		return null;
	}
	
}
