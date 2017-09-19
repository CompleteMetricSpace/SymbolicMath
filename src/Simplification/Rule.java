package Simplification;
import java.util.Vector;

import Expression.Expr;
import Expression.Operator;
import Symbolic.Constant;
import Symbolic.Greedy;
import Symbolic.Literal;
import Symbolic.Mobile;
import Symbolic.Num;
import Symbolic.Numerical;
import Symbolic.Symbolic;
import Symbolic.Var;
import Symbolic.Wild;


public class Rule
{
    Expr expression;
    Expr replace;
    Expr condition;
    Var[] vars;
    
    public Rule(Expr e, Expr r, Var[] v)
    {
    	expression = e;
    	replace = r;
    	vars = v;
    	condition = Constant.TRUE;
    }
    
    public Rule(Expr e, Expr r, Expr con, Var[] v)
    {
    	expression = e;
    	replace = r;
    	vars = v;
    	condition = con;
    }
    
    public Expr getExpr()
    {
    	return expression;
    }
    
    public Expr getReplacement()
    {
    	return replace;
    }
    
    public Expr getCondition()
    {
    	return condition;
    }
    
    public Var[] getVars()
    {
    	return vars;
    }
    
    
    
    public static Expr applyRule(Expr expr, Rule rule)
    {
    	Expr[] vs = match(expr, rule.getExpr(), rule.getVars());
    	if(vs != null)
    	{
    		Expr con = rule.getCondition().substitute(rule.getVars(), vs);
    		if(con.equals(Constant.TRUE))
    		{
    			Expr r = rule.getReplacement().substitute(rule.getVars(), vs);
    			if(!r.equals(expr))
    				return applyRule(r, rule);
    			else
    				return r;
    		}
    		
    	}
    	if(!(expr instanceof Symbolic))
    	{
    		Expr[] e = new Expr[expr.length()];
    		for(int i = 0;i<e.length;i++)
    			e[i] = applyRule(expr.get(i), rule);
    		Expr r = new Expr(expr.getOperator(), e);
    		if(!r.equals(expr))
    			return applyRule(r, rule);
    		else
    			return r;
    	}
    	return expr;
        
    }

	public static Expr[] match(Expr expr, Expr e, Expr[] v) 
	{
		if(v.length == 0 && expr.equals(e))
			return new Expr[]{};
		if(v.length == 0 && !expr.equals(e))
			return null;
		if(e instanceof Symbolic)
		{
			if(e instanceof Literal)
			{
				if(expr instanceof Var)
					return new Expr[]{expr};
				else
					return null;
			}
			if(e instanceof Num)
			{
				if(expr instanceof Numerical)
					return new Expr[]{expr};
				else
					return null;
			}
			
			if(e instanceof Wild || e instanceof Mobile)
			{
				return new Expr[]{expr};
			}
			return null;
		}
		if(expr instanceof Symbolic && !(e instanceof Symbolic))
			return null;
		if(!(expr instanceof Symbolic) && !(e instanceof Symbolic))
		{
			if(expr.length() < e.length() && !(e.get(e.length()-1) instanceof Greedy))
				return null;
			if(expr.length()+1 < e.length())
				return null;
			if(expr.length() > e.length() && !(e.get(e.length()-1) instanceof Greedy))
				return null;
			if(!expr.getOperator().equals(e.getOperator()))
				return null;
			
			for(int k = 0;k<e.length();k++)
			{
				if(e.get(k) instanceof Mobile)
				{
					Expr[] tmp = Set.remove(e.getOperands(),k);
					Mobile mb = (Mobile)e.get(k);
					for(int i = k;i<expr.length();i++)
					{
						//Create new match expression
						Expr mb_w = mb.getExpression();
						Expr[] args = Set.set(tmp, i, mb_w);
						
						Expr match = new Expr(e.getOperator(), args);
						Expr[] new_v = Set.substitute(v, mb, mb_w);
						Expr[] m = match(expr, match, new_v);
                        if(m != null)
                        {
                        	//int index = Set.indexOf(new_v, mb_w);
                        	return m;
                        }
                        else
                        	continue;
					}



				}
			}
			
			Expr[] list = new Expr[v.length];
			for(int i = 0;i<e.length();i++)
			{
				
				Expr e_sub = e.get(i);
				
				
				if(e_sub instanceof Greedy)
				{
					Expr[] gr = new Expr[expr.length()-i];
					
					for(int j = 0;j<gr.length;j++)
						gr[j] = expr.get(j+i);
					Expr s = new Expr(Operator.ARGS, gr);
					int index = Set.indexOf(v, e_sub);
					if(list[index] == null)
						list[index] = s;
					else
					{
						//a Wildcard cannot have different values
						if(!list[index].equals(s))
							return null;
					}
					return list;
				}
				Expr expr_sub = expr.get(i);
				//Create new Variable list of e_sub
				Vector<Expr> vars_new = new Vector<>();
				for(int j = 0;j<v.length;j++)
				{
					if(e_sub.contains(new Expr[]{v[j]}))
						vars_new.add(v[j]);
				}
				Expr[] v_new = vars_new.toArray(new Expr[vars_new.size()]);
				//recursive pattern matching
				Expr[] pm = match(expr_sub, e_sub, v_new);
				if(pm == null)
					return null;
				for(int j = 0;j<pm.length;j++)
				{
					int index = Set.indexOf(v, v_new[j]);
					if(list[index] == null)
						list[index] = pm[j];
					else
					{
						//a Wildcard cannot have different values
						if(!list[index].equals(pm[j]))
							return null;
					}
				}
				
				
			}
			return list;
		}
		return null;
	}
	
	
		
		
	
}
