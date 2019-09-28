package code;

import gui.InOut;

import java.io.Serializable;
import java.util.Vector;

import Expression.Expr;
import Symbolic.Constant;
import Symbolic.Var;
import Simplification.*;


public class Program  implements Serializable
{
	String name;
	int number_of_args;
    Line[] code;
    Var[] param; 
    

	
    public Program(String nm, Line[] cd, Var[] args)
    {
    	name = nm;
    	number_of_args = args.length;
    	code = cd;
    	param = args;
    }
    
  
    
    public String getName()
    {
    	return name;
    }
    
    public String toString()
    {
    	return name;
    }
    
    public Var[] getParameters() 
    {
		return param;
	}
    
    public ProgramReturn execute(Expr[] args) throws Exception 
    {
    	if(args.length != param.length)
    		throw new Exception("Program execution error: wrong number of arguments");
    	
    	//Initialize parameters
        Vector<Expr> values = new Vector<>();
        Vector<Var> vars = new Vector<>();
    	for(int i = 0;i<args.length;i++)
    	{
    		vars.add(param[i]);
    		values.add(args[i]);
    	}

    	//Begin to interpret the code
    	for(int i = 0;i<code.length;i++)
    	{
    		Line line = code[i];
    		if(line instanceof AssignmentLine)
    		{
    			Var[] v = ((AssignmentLine)line).getVariable();
    			Expr[] e = ((AssignmentLine)line).getExpression();
    			Expr[] es = new Expr[e.length];
    			for(int j = 0;j<es.length;j++)
    			    es[j] = e[j].substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    			Expr[] e_simp = new Expr[e.length];
    			for(int j = 0;j<es.length;j++)
    			    e_simp[j] = Simplification.simplify_recursive(es[j]);
    			boolean already_declared = false;
    			for(int k = 0;k<e_simp.length;k++)
    			{
    				for(int j = 0;j<vars.size();j++)
    				{
    					if(vars.get(j).equals(v[k]))
    					{
    						already_declared = true;
    						values.set(j, e_simp[k]);
    						break;
    					}
    				}

    				if(!already_declared)
    				{
    					vars.add(v[k]);
    					values.add(e_simp[k]);
    				}
    			}
    			continue;
    		}
    		if(line instanceof ReturnLine)
    		{
    			Expr e = ((ReturnLine)line).getReturn();
    			Expr es = e.substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    			Expr e_simp = Simplification.simplify_recursive(es);
    			return new ProgramReturn(e_simp,vars.toArray(new Var[vars.size()]),values.toArray(new Expr[values.size()]), "RETURN");
    		}
    		if(line instanceof WriteLine)
    		{
    			Expr e = ((WriteLine)line).getWriteExpr();
    			Expr es = e.substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    			Expr e_simp = Simplification.simplify_recursive(es);
    			InOut.program_output(e_simp.toString2());
    			continue;
    		}
    		if(line instanceof ForLine)
    		{
    			Line[] for_code = ((ForLine)line).getCode();
    			AssignmentLine al = ((ForLine)line).getAssignment();
    			Expr condition = ((ForLine)line).getCondition();
    			Line iteration = ((ForLine)line).getIteration();
    			
    			//Make assignment
    			Var[] v = al.getVariable();
    			Expr[] e = al.getExpression();
    			Expr[] es = new Expr[e.length];
    			for(int j = 0;j<es.length;j++)
    			    es[j] = e[j].substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    			Expr[] e_simp = new Expr[e.length];
    			for(int j = 0;j<es.length;j++)
    			    e_simp[j] = Simplification.simplify_recursive(es[j]);
    			boolean already_declared = false;
    			for(int k = 0;k<e_simp.length;k++)
    			{
    				for(int j = 0;j<vars.size();j++)
    				{
    					if(vars.get(j).equals(v[k]))
    					{
    						already_declared = true;
    						values.set(j, e_simp[k]);
    						break;
    					}
    				}

    				if(!already_declared)
    				{
    					vars.add(v[k]);
    					values.add(e_simp[k]);
    				}
    			}
    			
    			//Make condition
    			Expr cs = condition.substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    			Expr cond = Simplification.simplify_recursive(cs);
    			
    			while(true)
    			{
    				if(cond.equals(Constant.TRUE))
    				{
    					//Make new sub-program
    					Program sub_program = new Program(name+"_for_line:"+i, for_code, vars.toArray(new Var[vars.size()]));
    					//Execute sub-program with variables as arguments
    					ProgramReturn pr = sub_program.execute(values.toArray(new Expr[values.size()]));
    					//Rewrite sub-programs variables at the end to this programs variables 
    					//Only variables given as arguments are going to be rewritten:
    					for(int k = 0;k<pr.getVars().length;k++)
    					{
    						for(int j = 0;j<vars.size();j++)
    		    			{
    		    				if(vars.get(j).equals(pr.getVars()[k]))
    		    				{
    		    					values.set(j, pr.getValues()[k]);
    		    					break;
    		    				}
    		    			}
    					}
    					//Check if there was a return statement
    					if(pr.getEnd().equals("RETURN"))
    					{
    						return new ProgramReturn(pr.getReturnExpr(), vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "RETURN");
    					}
    					//Check if there was a break statement
    					if(pr.getEnd().equals("BREAK"))
    					{
    						break;
    					}
    					//If there wasn't, make iteration step:
    					Program iteration_program = new Program(name+"_it_line:"+i, new Line[]{iteration}, vars.toArray(new Var[vars.size()]));
    					ProgramReturn pr_it = iteration_program.execute(values.toArray(new Expr[values.size()]));
    					for(int k = 0;k<pr_it.getVars().length;k++)
    					{
    						for(int j = 0;j<vars.size();j++)
    		    			{
    		    				if(vars.get(j).equals(pr_it.getVars()[k]))
    		    				{
    		    					values.set(j, pr_it.getValues()[k]);
    		    					break;
    		    				}
    		    			}
    					}
    					if(pr_it.getEnd().equals("RETURN"))
    					{
    						return new ProgramReturn(pr_it.getReturnExpr(), vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "RETURN");
    					}			
    					//Then check condition:
                        cs = condition.substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    	    			cond = Simplification.simplify_recursive(cs);
    	    			continue;
    					
    				}
    				else
    				{
    				    if(cond.equals(Constant.FALSE))
    					    break;
    				    else
    				    	throw new Exception("Program execution error: condition didn't result in true or false: line: "+cond);
    				}
    			}
    			continue;
    		}
    		if(line instanceof WhileLine)
    		{
    			Line[] while_code = ((WhileLine)line).getCode();
    			Expr condition = ((WhileLine)line).getCondition();
    			
    			//Make condition
    			Expr cs = condition.substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    			Expr cond = Simplification.simplify_recursive(cs);
    			
    			while(true)
    			{
    				if(cond.equals(Constant.TRUE))
    				{
    					//Make new sub-program
    					Program sub_program = new Program(name+"_for_line:"+i, while_code, vars.toArray(new Var[vars.size()]));
    					//Execute sub-program with variables as arguments
    					ProgramReturn pr = sub_program.execute(values.toArray(new Expr[values.size()]));
    					//Rewrite sub-programs variables at the end to this programs variables 
    					//Only variables given as arguments are going to be rewritten:
    					for(int k = 0;k<pr.getVars().length;k++)
    					{
    						for(int j = 0;j<vars.size();j++)
    		    			{
    		    				if(vars.get(j).equals(pr.getVars()[k]))
    		    				{
    		    					values.set(j, pr.getValues()[k]);
    		    					break;
    		    				}
    		    			}
    					}
    					//Check if there was a return statement
    					if(pr.getEnd().equals("RETURN"))
    					{
    						return new ProgramReturn(pr.getReturnExpr(), vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "RETURN");
    					}
    					//Check if there was a break statement
    					if(pr.getEnd().equals("BREAK"))
    					{
    						break;
    					}
    					//Then check condition:
                        cs = condition.substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    	    			cond = Simplification.simplify_recursive(cs);
    	    			continue;
    					
 
    				}
    				else
    				{
    				    if(cond.equals(Constant.FALSE))
    					    break;
    				    else
    				    	throw new Exception("Program execution error: condition didn't result in true or false: line: "+i);
    				}
    			}
    			continue;
    		}
    		if(line instanceof Statement)
    		{
    			Statement s = (Statement)line;
    			if(s.equals(Statement.BREAK))
    			    return new ProgramReturn(null, vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "BREAK");
    			if(s.equals(Statement.CONTINUE))
    			    return new ProgramReturn(null, vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "CONTINUE");
    			continue;
    		}
    		if(line instanceof ConditionalLine)
    		{
    			Expr condition = ((ConditionalLine)line).getCondition();
    			Expr cs = condition.substitute(vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]));
    			Expr cond = Simplification.simplify_recursive(cs);
    			if(cond.equals(Constant.TRUE))
    			{
    				Line[] true_code = ((ConditionalLine)line).getTrueCode();
    				//Make new sub-program
					Program sub_program = new Program(name+"_for_line:"+i, true_code, vars.toArray(new Var[vars.size()]));
					//Execute sub-program with variables as arguments
					ProgramReturn pr = sub_program.execute(values.toArray(new Expr[values.size()]));
					//Rewrite sub-programs variables at the end to this programs variables 
					//Only variables given as arguments are going to be rewritten:
					for(int k = 0;k<pr.getVars().length;k++)
					{
						for(int j = 0;j<vars.size();j++)
		    			{
		    				if(vars.get(j).equals(pr.getVars()[k]))
		    				{
		    					values.set(j, pr.getValues()[k]);
		    					break;
		    				}
		    			}
					}
					//Check if there was a return statement
					if(pr.getEnd().equals("RETURN"))
					{
						return new ProgramReturn(pr.getReturnExpr(), vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "RETURN");
					}
					//Check if there was a break statement
					if(pr.getEnd().equals("BREAK"))
					{
						return new ProgramReturn(null, vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "BREAK");
					}
    			}
    			else
    			{
    				if(cond.equals(Constant.FALSE))
        			{
    					Line[] false_code = ((ConditionalLine)line).getFalseCode();
        				//Make new sub-program
    					Program sub_program = new Program(name+"_for_line:"+i, false_code, vars.toArray(new Var[vars.size()]));
    					//Execute sub-program with variables as arguments
    					ProgramReturn pr = sub_program.execute(values.toArray(new Expr[values.size()]));
    					//Rewrite sub-programs variables at the end to this programs variables 
    					//Only variables given as arguments are going to be rewritten:
    					for(int k = 0;k<pr.getVars().length;k++)
    					{
    						for(int j = 0;j<vars.size();j++)
    		    			{
    		    				if(vars.get(j).equals(pr.getVars()[k]))
    		    				{
    		    					values.set(j, pr.getValues()[k]);
    		    					break;
    		    				}
    		    			}
    					}
    					//Check if there was a return statement
    					if(pr.getEnd().equals("RETURN"))
    					{
    						return new ProgramReturn(pr.getReturnExpr(), vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "RETURN");
    					}
    					//Check if there was a break statement
    					if(pr.getEnd().equals("BREAK"))
    					{
    						return new ProgramReturn(null, vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "BREAK");
    					}
        			}
    				else
    					throw new Exception("Program execution error: condition didn't result in true or false: line: "+cond.toStringF());
    				
    			}
    		}
    		
    	}
    	return new ProgramReturn(null, vars.toArray(new Var[vars.size()]), values.toArray(new Expr[values.size()]), "END");

    }



	
}
