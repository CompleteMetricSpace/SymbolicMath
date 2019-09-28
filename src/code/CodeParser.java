package code;


import Expression.Expr;
import Expression.Parser;
import Symbolic.Var;

public class CodeParser 
{

	public static boolean isBetweenCodeWord(String s, int index)
	{
		int b = 0;
		for(int i = 0;i<s.length();i++)
		{
			boolean real_code_word = true;
			if(i > 0)
				real_code_word = !Parser.isLetter(s.charAt(i-1));
			if(s.startsWith("for(", i) && real_code_word)
			{
				b++;
				i = i + 4 - 1;
				continue;
			}
			if(s.startsWith("while(", i) && real_code_word)
			{
				b++;
				i = i + 6 - 1;
				continue;
			}
			if(s.startsWith("if(", i) && real_code_word)
			{
				b++;
				i = i + 3 - 1;
				continue;
			}
			if(s.startsWith("end", i) && real_code_word)
			{
				b--;
				i = i+3 - 1;
				continue;
			}
			if(i == index)
			{
				if(b == 0)
					return false;
				else
					return true;
			}
		}
		System.out.println("Error: don't know if between brackets");
		return false;
	}
	
	public static boolean isInBrackets(String s, int index)
	{
		int b = 0;
		for(int i = 0;i<s.length();i++)
		{
			if(s.charAt(i) == '(')
				b++;
			if(s.charAt(i) == ')')
				b--;
			if(i == index)
			{
				if(b == 0)
					return false;
				else
					return true;
			}
		}
		return false;
	}
	
	public static int findClosingBracket(String s, int br)
	{
		int b = 0;
		for(int i = br;i<s.length();i++)
		{
			if(s.charAt(i) == '(')
				b++;
			if(s.charAt(i) == ')')
				b--;
			if(b == 0)
				return i;
		}
		return -1; //No closing Bracket detected
	}
	
	
	
	public static Line[] parse(String code) throws Exception
	{
		code = code.trim();
		code = code.replaceAll("\n", "");
		//Split lines at semicolons ;
		int indexSemicolon = code.indexOf(';');
		while(indexSemicolon != -1 && isBetweenCodeWord(code, indexSemicolon))
			indexSemicolon = code.indexOf(';', indexSemicolon+1);
		if(indexSemicolon == -1)
			return new Line[]{};
		else
		{
			
			String line = code.substring(0, indexSemicolon);
			String rest = code.substring(indexSemicolon+1, code.length());
			Line[] rest_code = parse(rest);
			Line this_line = null;
			
			
			if(line.startsWith("for")) //ForLine
			{
				int cb = findClosingBracket(line, 3);
				String args = line.substring(4, cb);
				//Parse
				int indexComma = args.indexOf(',');
				while(indexComma != -1 && isInBrackets(args, indexComma))
					indexComma = args.indexOf(',', indexComma+1);
				int indexComma2 = args.indexOf(',', indexComma+1);
				while(indexComma2 != -1 && isInBrackets(args, indexComma2))
					indexComma2 = args.indexOf(',', indexComma2+1);
				String _1 = args.substring(0, indexComma);
				String _2 = args.substring(indexComma+1, indexComma2);
				String _3 = args.substring(indexComma2+1, args.length());
				AssignmentLine as = (AssignmentLine)parse(_1+";")[0];
				Expr cond = Parser.parse(_2);
				Line iter = parse(_3+";")[0];
				
				//Parse body
				String body = line.substring(cb+1, line.length()-3);
				Line[] bd = parse(body);
				this_line = new ForLine(as, cond, iter, bd);
			}
			else
			if(line.startsWith("while")) //WhileLine
			{
				int cb = findClosingBracket(line, 5);
				String args = line.substring(6, cb);
				Expr cond = Parser.parse(args);
				String body = line.substring(cb+1, line.length()-3);
				Line[] bd = parse(body);
				this_line = new WhileLine(cond, bd);
				
			}
			else
			if(line.startsWith("if")) //ConditionalLine
			{
				int cb = findClosingBracket(line, 2);
				String args = line.substring(3, cb);
				Expr cond = Parser.parse(args);
				String body = line.substring(cb+1, line.length()-3);
				int indexElse = body.indexOf("else");
				while(indexElse != -1 && isBetweenCodeWord(body, indexElse))
				    indexElse = body.indexOf("else", indexElse+1);
				if(indexElse == -1)
				{
					Line[] bd = parse(body);
					this_line = new ConditionalLine(cond, bd);
				}
				else
				{
					Line[] bd_true = parse(body.substring(0, indexElse));
					Line[] bd_false = parse(body.substring(indexElse+4, body.length()));
					this_line = new ConditionalLine(cond, bd_true, bd_false);
					
				}
			}
			else
			if(line.startsWith("write")) //WriteLine
			{
				int cb = findClosingBracket(line, 5);
				String args = line.substring(6, cb);
				Expr wrt = Parser.parse(args);
				this_line = new WriteLine(wrt);
			}
			else
			if(line.contains(":=")) //AssignmentLine
			{
				int index = line.indexOf(":=");
				String v = line.substring(0, index);
				String e = line.substring(index+2, line.length());
				//Parallel Assignment
				if(v.startsWith("[") && v.endsWith("]"))
				{
					if(e.startsWith("[") && e.endsWith("]"))
					{
						Expr[] vars = Parser.parseArgs(v.substring(1, v.length()-1));
						Expr[] exprs = Parser.parseArgs(e.substring(1, e.length()-1));
						Var[] vars_v = new Var[vars.length];
						for(int i = 0;i<vars.length;i++)
						{
							if(!vars[i].isVar())
								throw new Exception("Program parser exception: assignment not to a variable");
							vars_v[i] = (Var)vars[i];
						}
						if(vars.length != exprs.length)
							throw new Exception("Program parser exception: number of variables not equal to number of expressions in assignment");
						this_line = new AssignmentLine(vars_v, exprs);
					}
					else
					{
						throw new Exception("Program parser exception: number of variables not equal to number of expressions in assignment");
					}
				}
				else
				{
					Expr var = Parser.parse(v);
					Expr expr = Parser.parse(e);
					if(!var.isVar())
						throw new Exception("Program parser exception: assignment not to a variable");
					this_line = new AssignmentLine(new Var[]{(Var)var}, new Expr[]{expr});
				}
			}
			else
			if(line.equals("break"))
			{
				this_line = Statement.BREAK;
			}
			else
			if(line.equals("continue"))
			{
				this_line = Statement.CONTINUE;
			}
			else
			if(line.startsWith("return"))
			{
				String ret = line.substring(6);
				Expr expr = Parser.parse(ret);
				this_line = new ReturnLine(expr);
			}
			
			Line[] all = new Line[rest_code.length+1];
			all[0] = this_line;
			for(int i = 1;i<all.length;i++)
				all[i] = rest_code[i-1];
			return all;
		}	
	}
	
	
	
}
