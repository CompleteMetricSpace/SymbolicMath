package calculus;

import Expression.Expr;
import Expression.Operator;
import Symbolic.Constant;
import Symbolic.DExtension;
import Symbolic.Int;
import Symbolic.Rational;

public class Diff 
{
    public static Expr derivative(Expr u, Expr x)
    {
    	if(x.equals(Constant.VOID))
    	{
    		if(u.isVar())
    			return new Expr(Operator.TOTAL_DIFFERENTIAL, u);
    		if(u.isNumerical())
    			return Int.ZERO;
    	}
    	if(u.equals(x))
    		return Int.ONE;
    	if(u instanceof DExtension)
    	{
    		DExtension d = (DExtension)u;
    		if(d.isLog())
    			return derivative(d.getArg(), x).div(d.getArg());
    		if(d.isExp())
    			return derivative(d.getArg(), x).mul(d);
    		if(d.isX())
    			if(d.equals(x))
    				return Int.ONE;
    			else
    				return Int.ZERO;
       	}
    	if(u.isFreeOf(x) && !(u instanceof DExtension) && (!x.equals(Constant.VOID)))
    		return Int.ZERO;
    	if(u.isPower())
    	{
    		Expr b = u.get(0);
    		Expr e = u.get(1);
    		if(b.equals(x) && e.isFreeOf(x))
    			return e.mul(b.pow(e.sub(Int.ONE)));
    		Expr b_p = derivative(b, x);
    		Expr e_p = derivative(e, x);
    		return u.mul(e.mul(b_p).div(b).add(new Expr(Operator.LOG, b).mul(e_p)));
    	}
    	if(u.isSum())
    	{
    		Expr v = u.get(0);
    		Expr w = u.sub(v);
    		return derivative(v, x).add(derivative(w, x));
    	}
    	if(u.isProduct())
    	{
    		Expr n = Int.ZERO;
    		for(int i = 0;i<u.length();i++)
    		{
    			Expr d = derivative(u.get(i), x);
    			Expr p = Int.ONE;
    			for(int j = 0;j<u.length();j++)
    			{
    				if(j == i)
    					p = p.mul(d);
    				else
    					p = p.mul(u.get(j));
    			}
    			n = n.add(p);
    		}
    		return n;
    	}
    	if(u.getOperator().equals(Operator.EXP))
    	{
    		Expr v = derivative(u.get(0), x);
    		return v.mul(u);
    	}
    	if(u.getOperator().equals(Operator.LOG))
    	{
    		Expr v = derivative(u.get(0), x);
    		return v.div(u.get(0));
    	}
    	if(u.getOperator().equals(Operator.SIN))
    	{
    		Expr v = derivative(u.get(0), x);
    		return new Expr(Operator.COS, u.get(0)).mul(v);
    	}
    	if(u.getOperator().equals(Operator.COS))
    	{
    		Expr v = derivative(u.get(0), x);
    		return new Expr(Operator.SIN, u.get(0)).mul(v).mul(Int.NONE);
    	}
    	if(u.getOperator().equals(Operator.TAN))
    	{
    		Expr v = derivative(u.get(0), x);
    		return new Expr(Operator.TAN, u.get(0)).pow(Int.TWO).mul(v).add(v);
    	}
    	if(u.getOperator().equals(Operator.SINH))
    	{
    		Expr v = derivative(u.get(0), x);
    		return new Expr(Operator.COSH, u.get(0)).mul(v);
    	}
    	if(u.getOperator().equals(Operator.COSH))
    	{
    		Expr v = derivative(u.get(0), x);
    		return new Expr(Operator.SINH, u.get(0)).mul(v);
    	}
    	if(u.getOperator().equals(Operator.ARCSIN))
    	{
    		Expr v = derivative(u.get(0), x);
    		return v.div(Int.ONE.sub(u.get(0).pow(Int.TWO)).pow(Rational.HALF));
    	}
    	if(u.getOperator().equals(Operator.ARCCOS))
    	{
    		Expr v = derivative(u.get(0), x);
    		return Int.NONE.mul(v).div(Int.ONE.sub(u.get(0).pow(Int.TWO)).pow(Rational.HALF));
    	}
    	if(u.getOperator().equals(Operator.ARCTAN))
    	{
    		Expr v = derivative(u.get(0), x);
    		return v.div(u.get(0).pow(Int.TWO).add(Int.ONE));
    	}
    	if(u.length() == 1)
    	{
    		Expr v = u.get(0);
    		return derivative(v, x).mul(new Expr(Operator.FDERIV, u.getOperator(), Int.ONE, v));
    	}
    	
    	if(u.getOperator().equals(Operator.FDERIV))
    	{
    		Expr f = u.get(0);
    		Expr[] list = u.get(1).isList()?u.get(1).getOperands():new Expr[]{u.get(1)};
    		Expr[] vars = u.get(2).isList()?u.get(2).getOperands():new Expr[]{u.get(2)};
    		Expr d = Int.ZERO;
    		for(int i = 0;i<list.length;i++)
    		{
    			Expr[] n = new Expr[list.length];
    			for(int j = 0;j<list.length;j++)
    			{
    				if(j == i)
    					n[j] = list[j].add(Int.ONE);
    				else
    					n[j] = list[j];
    			}
    			d = d.add(new Expr(Operator.FDERIV, f, new Expr(Operator.LIST, n), new Expr(Operator.LIST, vars)).mul(Diff.derivative(vars[i], x)));
    		}
    		return d;
    	}
    	if(u.length() > 1)
    	{
    		Expr d = Int.ZERO;
    		for(int i = 0;i<u.length();i++)
    		{
    			Expr[] n = new Expr[u.length()];
    			for(int j = 0;j<n.length;j++)
    			{
    				if(j == i)
    					n[j] = Int.ONE;
    				else
    					n[j] = Int.ZERO;
    			}
    			d = d.add(new Expr(Operator.FDERIV, u.getOperator(), new Expr(Operator.LIST, n), new Expr(Operator.LIST, u.getOperands())).mul(Diff.derivative(u.get(i), x)));
    		}
    		return d;
    	}
    	return new Expr(Operator.DERIV, u, x);
    }
	
	
}
