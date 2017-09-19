package algebra;

import java.util.Vector;

import polynomial.GroebnerBasis;
import polynomial.Poly;
import Expression.Expr;
import Expression.Operator;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;

public class FunctionTransforms 
{
     public static Expr expand_exp(Expr u)
     {
    	 if(u.isSymbolic())
    		 return u;
    	 Expr[] op = new Expr[u.length()];
    	 for(int i = 0;i<u.length();i++)
    		 op[i] = expand_exp(u.get(i));
    	 Expr v = Simplification.simplify_recursive(new Expr(u.getOperator(), op));
    	 if(v.getOperator().equals(Operator.EXP))
    	 {
    		return expand_exp_rules(v.get(0));
    	 }
    	 return v;
     }
     
     private static Expr expand_exp_rules(Expr A)
     {
		 if(A.isSum())
		 {
			 Expr f = A.get(0);
			 return expand_exp_rules(f).mul(expand_exp_rules(A.sub(f)));
		 }
		 if(A.isProduct())
		 {
			 Expr f = A.get(0);
			 if(f.isInt())
			 {
				 return expand_exp_rules(A.div(f)).pow(f);
			 }
		 }
		 return new Expr(Operator.EXP, A);
     }
     
     public static Expr expand_log(Expr u)
     {
    	 if(u.isSymbolic())
    		 return u;
    	 Expr[] op = new Expr[u.length()];
    	 for(int i = 0;i<u.length();i++)
    		 op[i] = expand_log(u.get(i));
    	 Expr v = Simplification.simplify_recursive(new Expr(u.getOperator(), op));
    	 if(v.getOperator().equals(Operator.LOG))
    	 {
    		return expand_log_rules(v.get(0));
    	 }
    	 return v;
     }
     
     private static Expr expand_log_rules(Expr A)
     {
		 if(A.isProduct())
		 {
			 Expr f = A.get(0);
			 return expand_log_rules(f).add(expand_log_rules(A.div(f)));
		 }
		 if(A.isPower())
		 {
			 Expr f = A.get(0);
			 Expr e = A.get(1);
			 if(e.isInt())
			 {
				 return expand_log_rules(f).mul(e);
			 }
		 }
		 return new Expr(Operator.LOG, A);
     }
     
     public static Expr contract_exp(Expr u)
     {
    	 if(u.isSymbolic())
    		 return u;
    	 Expr[] op = new Expr[u.length()];
    	 for(int i = 0;i<u.length();i++)
    		 op[i] = contract_exp(u.get(i));
    	 Expr v = Simplification.simplify_recursive(new Expr(u.getOperator(), op));
    	 if(v.isProduct() || v.isPower())
    		 return contract_exp_rules(v);
    	 return v;
     }
     
     private static Expr contract_exp_rules(Expr u)
     {
    	 Expr v = Algebra.weak_expand(u);
    	 if(v.isPower())
    	 {
    		 Expr b = v.get(0);
    		 Expr s = v.get(1);
    		 if(b.getOperator().equals(Operator.EXP))
    		 {
    			 Expr p = b.get(0).mul(s);
    			 if(p.isProduct() || p.isPower())
    				 p = contract_exp_rules(p);
    			 return new Expr(Operator.EXP, p);
    		 }
    		 else
    			 return v;
    	 }
    	 if(v.isProduct())
    	 {
    		 Expr p = Int.ONE;
    		 Expr s = Int.ZERO;
    		 for(int i = 0;i<v.length();i++)
    		 {
    			 Expr A = v.get(i);
    			 if(A.getOperator().equals(Operator.EXP))
    				 s = s.add(A.get(0));
    			 else
    				 p = p.mul(A);
    		 }
    		 return new Expr(Operator.EXP, s).mul(p);
    	 }
    	 if(v.isSum())
    	 {
    		 Expr s = Int.ZERO;
    		 for(int i = 0;i<v.length();i++)
    		 {
    			 Expr A = v.get(i);
    			 if(A.isProduct() || A.isSum())
    				 s = s.add(contract_exp_rules(A));
    			 else
    				 s = s.add(A);
    		 }
    		 return s;
    	 }
    	 return v;
     }
     
     public static Expr contract_log(Expr u)
     {
    	 if(u.isSymbolic())
    		 return u;
    	 Expr[] op = new Expr[u.length()];
    	 for(int i = 0;i<u.length();i++)
    		 op[i] = contract_log(u.get(i));
    	 Expr v = Simplification.simplify_recursive(new Expr(u.getOperator(), op));
    	 if(v.isSum() || v.isProduct())
    		 return contract_log_rules(v);
    	 return v;
     }
     
     private static Expr contract_log_rules(Expr v)
     {
    	 if(v.isProduct())
    	 {
    		 Expr b = v.get(0);
    		 if(b.isInt())
    		 {
        		 Expr s = Int.ONE;
        		 boolean collected = false;
        		 for(int i = 1;i<v.length();i++)
        		 {
        			 Expr A = v.get(i);
        			 if(A.getOperator().equals(Operator.LOG) && !collected)
        			 {
        				 collected = true;
        				 s = s.mul(new Expr(Operator.LOG, contract_log_rules(A.get(0).pow(b))));
        			 }
        			 else
        				 s = s.mul(A);
        		 }
        		 if(collected)
        			 return s;
        		 else
        			 return s.mul(b);
    		 }
    	 }
    	 if(v.isSum())
    	 {
    		 Expr p = Int.ZERO;
    		 Expr s = Int.ONE;
    		 for(int i = 0;i<v.length();i++)
    		 {
    			 Expr A = v.get(i);
    			 if(A.getOperator().equals(Operator.LOG))
    				 s = s.mul(A.get(0));
    			 else
    				 p = p.add(A);
    		 }
    		 return new Expr(Operator.LOG, s).add(p);
    	 }
    	 
    	 return v;
     }
     
     public static Expr expand_trig(Expr u)
     {
    	 if(u.isSymbolic())
    		 return u;
    	 Expr[] V = new Expr[u.length()];
    	 for(int i = 0;i<V.length;i++)
    		 V[i] = expand_trig(u.get(i));
    	 Expr v = Simplification.simplify_recursive(new Expr(u.getOperator(), V));
    	 if(v.getOperator().equals(Operator.SIN))
    		 return expand_trig_rules(v.get(0))[0];
    	 if(v.getOperator().equals(Operator.COS))
    		 return expand_trig_rules(v.get(0))[1];
    	 return v;
     }
     
     public static Expr[] expand_trig_rules(Expr A)
     {
    	 if(A.isSum())
    	 {
    		 Expr[] f = expand_trig_rules(A.get(0));
    		 Expr[] r = expand_trig_rules(A.sub(A.get(0)));
    		 Expr s = Algebra.expand(f[0].mul(r[1]).add(r[0].mul(f[1])));
    		 Expr c = Algebra.expand(f[1].mul(r[1]).sub(r[0].mul(f[0])));
    		 return new Expr[]{s, c};
    	 }
    	 if(A.isProduct())
    	 {
    		 Expr f = A.get(0);
    		 if(f.isInt())
    		 {
    			 Expr r = A.div(f);
    			 return new Expr[]{multiple_angle_sin((Int)f, r), multiple_angle_cos((Int)f, r)};
    		 }
    	 }
    	 return new Expr[]{new Expr(Operator.SIN, A), new Expr(Operator.COS, A)};
     }
     
     private static Expr multiple_angle_cos(Int n, Expr u) 
     {
    	 if(n.isNegative())
    		n = n.abs();
    	 Expr sum = Int.ZERO;
    	 Expr[] sc = expand_trig_rules(u);
    	 for(Int j = Int.ZERO;j.compareTo(n)<=0;j = j.add(Int.TWO))
    	 {
    		 sum = sum.add(Int.NONE.pow(j.div(Int.TWO)).mul(Int.binom(n, j))
    				 .mul(Algebra.expand(sc[1].pow(n.sub(j)).mul(sc[0].pow(j)))));
    	 }
    	 return sum;	 
     }

     private static Expr multiple_angle_sin(Int n, Expr u) 
     {
    	 boolean negative = false;
    	 if(n.isNegative())
    	 {
    		 n = n.abs();
    		 negative = true;
    	 }
     	 Expr sum = Int.ZERO;
     	 Expr[] sc = expand_trig_rules(u);
     	 for(Int j = Int.ONE;j.compareTo(n)<=0;j = j.add(Int.TWO))
     	 {
     		 sum = sum.add(Int.NONE.pow(j.sub(Int.ONE).div(Int.TWO)).mul(Int.binom(n, j))
     				 .mul(Algebra.expand(sc[1].pow(n.sub(j)).mul(sc[0].pow(j)))));
     	 }
     	 if(!negative)
     	     return sum;
     	 else
     		 return Int.NONE.mul(sum);
     }

     public static Expr contract_all(Expr u)
     {
    	 Expr old;
    	 do
    	 { 
    		 old = u;
    		 u = contract_exp(u);
    		 u = contract_log(u);
    	 }
    	 while(!old.equals(u));
    	 return u;
     }

     public static Expr expand_all(Expr u)
     {
    	 Expr old;
    	 do
    	 { 
    		 old = u;
    		 u = expand_exp(u);
    		 u = expand_log(u);
    		 u = expand_trig(u);
    	 }
    	 while(!old.equals(u));
    	 return u;
     }
     
     public static Expr to_tan(Expr u)
     {
    	 if(u.isSymbolic())
    	     return u;
    	 Expr[] v = new Expr[u.length()];
    	 for(int i = 0;i<v.length;i++)
    		 v[i] = to_tan(u.get(i));
    	 Expr U = Simplification.simplify_recursive(new Expr(u.getOperator(), v));
    	 if(U.isProduct())
    	 {
    		 Expr r = Int.ONE;
    		 Vector<Expr> sin = new Vector<Expr>(); 
    		 Vector<Int> exp_sin = new Vector<Int>();
    		 Vector<Expr> cos = new Vector<Expr>(); 
    		 Vector<Int> exp_cos = new Vector<Int>();
    		 for(int i = 0;i<U.length();i++)
    		 {
    			 Expr A = U.get(i);
    			 Expr b = A.isPower()?A.get(0):A;
    			 Expr e = A.isPower()?A.get(1):Int.ONE;
    			 if(b.getOperator().equals(Operator.SIN) && e.isInt())
    			 {
    				 sin.add(b.get(0));
    				 exp_sin.add((Int)e);
    			 }
    			 else if(b.getOperator().equals(Operator.COS) && e.isInt())
    			 {
    				 cos.add(b.get(0));
    				 exp_cos.add((Int)e);
    			 }
    			 else
    				 r = r.mul(A);
    		 }
    		 for(int i = 0;i<sin.size();i++)
    		 {
    			 Expr a = sin.get(i);
    			 for(int j = 0;j<cos.size();j++)
    			 {
    				 Expr b = cos.get(j);
    				 if(a.equals(b))
    				 {
    					 Int m = exp_sin.get(i);
    					 Int n = exp_cos.get(j);
    					 if(m.isPositive() && n.isPositive())
    						 continue;
    					 if(m.isNegative() && n.isNegative())
    						 continue;
    					 if(m.equals(n.mul(Int.NONE)))
    					 {
    						 r = r.mul(new Expr(Operator.TAN, a).pow(m));
    						 cos.remove(j);
    						 exp_cos.remove(j);
    						 sin.remove(i);
    						 exp_sin.remove(i);
    						 i = i - 1;
    						 break;
    					 }
    					 if(m.isPositive() && n.isNegative())
    					 {
    						 n = n.mul(Int.NONE);
    						 if(m.compareTo(n) > 0)
    						 {
    							 Int s = m.sub(n);
    							 r = r.mul(new Expr(Operator.TAN, a).pow(n));
    							 r = r.mul(new Expr(Operator.SIN, a).pow(s));
    							 cos.remove(j);
    							 exp_cos.remove(j);
        						 sin.remove(i);
        						 exp_sin.remove(i);
        						 i = i - 1;
        						 break;
    						 }
    						 else
    						 {
    							 Int s = m.sub(n);
    							 r = r.mul(new Expr(Operator.TAN, a).pow(m));
    							 r = r.mul(new Expr(Operator.COS, a).pow(s));
    							 cos.remove(j);
    							 exp_cos.remove(j);
        						 sin.remove(i);
        						 exp_sin.remove(i);
        						 i = i - 1;
        						 break; 
    						 }
    					 }
    					 else
    					 {
    						 m = m.mul(Int.NONE);
    						 if(m.compareTo(n) > 0)
    						 {
    							 Int s = n.sub(m);
    							 r = r.div(new Expr(Operator.TAN, a).pow(n));
    							 r = r.mul(new Expr(Operator.SIN, a).pow(s));
    							 cos.remove(j);
    							 exp_cos.remove(j);
        						 sin.remove(i);
        						 exp_sin.remove(i);
        						 i = i - 1;
        						 break;
    						 }
    						 else
    						 {
    							 Int s = n.sub(m);
    							 r = r.div(new Expr(Operator.TAN, a).pow(m));
    							 r = r.mul(new Expr(Operator.COS, a).pow(s));
    							 cos.remove(j);
    							 exp_cos.remove(j);
        						 sin.remove(i);
        						 exp_sin.remove(i);
        						 i = i - 1;
        						 break; 
    						 }
    					 }
    				 }
    			 }
    		 }
    		 for(int i = 0;i<sin.size();i++)
    			 r = r.mul(new Expr(Operator.SIN, sin.get(i)).pow(exp_sin.get(i)));
    		 for(int i = 0;i<cos.size();i++)
    			 r = r.mul(new Expr(Operator.COS, cos.get(i)).pow(exp_cos.get(i)));
    		 return r;
    	 }
    	 return U;
     }
     
     public static Expr contract_trig(Expr u)
     {
    	 if(u.isSymbolic())
    		 return u;
    	 Expr[] v = new Expr[u.length()];
    	 for(int i = 0;i<v.length;i++)
    		 v[i] = contract_trig(u.get(i));
    	 Expr U = Simplification.simplify_recursive(new Expr(u.getOperator(), v));
    	 if(U.isPower() || U.isProduct())
    		 return contract_trig_rules(U);
    	 return U;
     }

	private static Expr contract_trig_rules(Expr u)
	{
		Expr v = Algebra.weak_expand(u);
		if(v.isPower())
			return contract_trig_power(v);
		if(v.isProduct())
		{
			Expr[] s = separate_sin_cos(v);
			Expr c = s[0];
			Expr d = s[1];
			if(d.equals(Int.ONE))
				return v;
			if(d.getOperator().equals(Operator.SIN) || d.getOperator().equals(Operator.COS))
				return v;
			if(d.isPower())
				return Algebra.weak_expand(c.mul(contract_trig_power(d)));
			if(d.isProduct())
				return Algebra.weak_expand(c.mul(contract_trig_product(d)));
			return v;
		}
		if(v.isSum())
		{
			Expr s = Int.ZERO;
			for(int i = 0;i<v.length();i++)
			{
				Expr y = v.get(i);
				if(y.isPower() || y.isProduct())
					s = s.add(contract_trig_rules(y));
				else
					s = s.add(y);
			}
			return s;
		}
	    return v;
	}
     
    private static Expr[] separate_sin_cos(Expr u)
    {
		if(u.isProduct())
		{
			Expr s = Int.ONE;
			Expr r = Int.ONE;
			for(int i = 0;i<u.length();i++)
			{
				Expr[] be = Simplification.base_exp(u.get(i));
				if(be[1].isNaturalNumber())
				{
					if(be[0].getOperator().equals(Operator.SIN) || be[0].getOperator().equals(Operator.COS))
					    s = s.mul(u.get(i));
					else
						r = r.mul(u.get(i));
				}
				else
					r = r.mul(u.get(i));
			}
			return new Expr[]{r, s};
		}
		Expr[] be = Simplification.base_exp(u);
		if(be[1].isNaturalNumber())
		{
			if(be[0].getOperator().equals(Operator.SIN) || be[0].getOperator().equals(Operator.COS))
			    return new Expr[]{Int.ONE, u};
		}
		return new Expr[]{u, Int.ONE};
	}

	private static Expr contract_trig_product(Expr u)
    {
    	if(u.length() == 2)
    	{
    		Expr A = u.get(0);
    		Expr B = u.get(1);
    		if(A.isPower())
    		{
    			A = contract_trig_power(A);
    			return contract_trig_rules(A.mul(B));
    		}
    		if(B.isPower())
    		{
    			B = contract_trig_power(B);
    			return contract_trig_rules(A.mul(B));
    		}
    		Expr theta = A.get(0);
    		Expr phi = B.get(0);
    		if(A.getOperator().equals(Operator.SIN) && B.getOperator().equals(Operator.SIN))
    			return theta.sub(phi).cos().div(Int.TWO).sub(theta.add(phi).cos().div(Int.TWO));
    		if(A.getOperator().equals(Operator.COS) && B.getOperator().equals(Operator.COS))
    			return theta.add(phi).cos().div(Int.TWO).add(theta.sub(phi).cos().div(Int.TWO));
    		if(A.getOperator().equals(Operator.SIN) && B.getOperator().equals(Operator.COS))
    			return theta.add(phi).sin().div(Int.TWO).add(theta.sub(phi).sin().div(Int.TWO));
    		if(A.getOperator().equals(Operator.COS) && B.getOperator().equals(Operator.SIN))
    			return theta.add(phi).sin().div(Int.TWO).add(phi.sub(theta).sin().div(Int.TWO));
    		return u;
    	}
    	else
    	{
    		Expr A = u.get(0);
    		Expr B = contract_trig_product(u.div(A));
    		return contract_trig_rules(A.mul(B));
    	}
    }

	private static Expr contract_trig_power(Expr u)
	{
		Expr[] be = Simplification.base_exp(u);
		if(be[1].isNaturalNumber())
		{
			Int n = (Int)be[1];
			if(be[0].getOperator().equals(Operator.COS))
			{
				Expr t = be[0].get(0);
				if(!n.isOdd())
				{
					Int b = n.divide(Int.TWO).sub(Int.ONE);
					Expr sum = Int.ZERO;
					for(Int j = Int.ZERO;j.compareTo(b) <= 0;j = j.add(Int.ONE))
						sum = sum.add(Int.binom(n, j).mul(n.sub(Int.TWO.mul(j)).mul(t).cos()));
					Int tp = (Int)Int.TWO.pow(n.sub(Int.ONE));
					return Int.binom(n, n.divide(Int.TWO)).div(Int.TWO.mul(tp)).add(sum.div(tp));
				}
				else
				{
					Int b = n.divide(Int.TWO);
					Expr sum = Int.ZERO;
					for(Int j = Int.ZERO;j.compareTo(b) <= 0;j = j.add(Int.ONE))
						sum = sum.add(Int.binom(n, j).mul(n.sub(Int.TWO.mul(j)).mul(t).cos()));
					Int tp = (Int)Int.TWO.pow(n.sub(Int.ONE));
					return sum.div(tp);
				}
			}
			if(be[0].getOperator().equals(Operator.SIN))
			{
				Expr t = be[0].get(0);
				if(!n.isOdd())
				{
					Int b = n.divide(Int.TWO).sub(Int.ONE);
					Expr sum = Int.ZERO;
					for(Int j = Int.ZERO;j.compareTo(b) <= 0;j = j.add(Int.ONE))
						sum = sum.add(Int.NONE.pow(j).mul(Int.binom(n, j).mul(n.sub(Int.TWO.mul(j)).mul(t).cos())));
					Int tp = (Int)Int.TWO.pow(n.sub(Int.ONE));
					return Int.NONE.pow(n).mul(Int.binom(n, n.divide(Int.TWO)).div(Int.TWO.mul(tp))).add(sum.div(tp).mul(Int.NONE.pow(n.divide(Int.TWO))));
				}
				else
				{
					Int b = n.divide(Int.TWO);
					Expr sum = Int.ZERO;
					for(Int j = Int.ZERO;j.compareTo(b) <= 0;j = j.add(Int.ONE))
						sum = sum.add(Int.NONE.pow(j).mul(Int.binom(n, j).mul(n.sub(Int.TWO.mul(j)).mul(t).sin())));
					Int tp = (Int)Int.TWO.pow(n.sub(Int.ONE));
					return sum.div(tp).mul(Int.NONE.pow(n.sub(Int.ONE).div(Int.TWO)));
				}
			}
		}
		return u;
	}
	
	

}
