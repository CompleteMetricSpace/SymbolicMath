package calculus;

import java.util.Vector;

import polynomial.BasicPoly;
import polynomial.Cancel;
import polynomial.Factor;
import polynomial.Poly;
import algebra.Algebra;
import algebra.FunctionTransforms;
import algebra.MatchForm;
import Expression.Expr;
import Expression.Operator;
import Expression.Parser;
import Expression.RecursionLimitReachedException;
import Simplification.Rule;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.*;

public class HeuristicIntegrate 
{
	public static int RECURSIVE_INTEGRATION = 50;
	public static int IT = 0;
	
	public static Expr integrate(Expr u, Expr x) throws RecursionLimitReachedException
	{
		IT = 0;
		return integrate_recursive(u, x);
	}

	public static Expr integrate_recursive(Expr u, Expr x) throws RecursionLimitReachedException
	{
		if(IT > RECURSIVE_INTEGRATION)
			throw new RecursionLimitReachedException("HeuristicIntegrate", IT);
		IT = IT + 1;
		Expr ans = integrate_table(u, x);
		if(!ans.equals(Constant.FAIL))
			return ans;
		ans = integrate_linear_properties(u, x);
		if(!ans.equals(Constant.FAIL))
			return ans;
		ans = integrate_substitution(u, x);
		if(!ans.equals(Constant.FAIL))
			return ans;
		ans = integrate_substitution_fractional_exponent(u, x);
		if(!ans.equals(Constant.FAIL))
			return ans;
		ans = integrate_rational(u, x);
		if(!ans.equals(Constant.FAIL))
			return ans;
		ans = integrate_by_parts(u, x);
		if(!ans.equals(Constant.FAIL))
			return ans;
		
		Expr g = FunctionTransforms.contract_trig(u);
		if(!g.equals(u))
		{
			ans = integrate_recursive(g, x);
			if(!ans.equals(Constant.FAIL))
				return ans;
		}
		
		g = Algebra.expand(u);
		if(!g.equals(u) && !Poly.is_rational_f(u))
		{
			ans = integrate_recursive(g, x);
			if(!ans.equals(Constant.FAIL))
				return ans;
		}
		return Constant.FAIL;
	}

	public static Expr integrate_substitution_fractional_exponent(Expr u, Expr x) throws RecursionLimitReachedException
	{
		Int lcm = Algebra.get_fraction_exponent_lcm(u, x);
		if(lcm.equals(Int.ONE))
			return Constant.FAIL;
		Expr v = x.pow(lcm);
		Expr dx = lcm.mul(x.pow(lcm.sub(Int.ONE)));
		Expr subst = Simplification.simplify_recursive(u.substitute(x, v));
		subst = Simplification.simplify_power_fraction(subst, x);
		subst = subst.mul(dx);
		Expr integral = integrate_recursive(subst, x);
		if(integral.equals(Constant.FAIL))
			return Constant.FAIL;
		integral = Simplification.simplify_recursive(integral.substitute(x, x.pow(Int.ONE.div(lcm))));
		return integral;
	}

	public static Expr integrate_substitution(Expr u, Expr x) throws RecursionLimitReachedException
	{
		Expr[] s = substitutions(u, x);
		Expr y = Simplification.getNewVariables(1, u, x)[0];
		int i = 0;
		Expr F = Constant.FAIL;
		while(F.equals(Constant.FAIL) && i<s.length)
		{
			Expr g = s[i];
			if(!g.equals(x) && !g.isFreeOf(x))
			{
				Expr f = u.substitute(g, y);
				Expr d = Diff.derivative(g, x);
				d = d.substitute(g, y);
				f = Algebra.cancel(f.div(d));
				if(f.isFreeOf(x))
					F = Simplification.simplify_recursive(integrate_recursive(f, y).substitute(y, g));
				else
				{
					//Special substitutions
				}
			}
			i = i + 1;
		}
		return F;
	}

	public static Expr[] substitutions(Expr u, Expr x)
	{
		if(u.isSymbolic())
	        return new Expr[]{};
		Expr[] s = new Expr[]{};
		for(int i = 0;i<u.length();i++)
			s = Set.union(s, substitutions(u.get(i), x));
		if(u.isPower())
			return Set.union(s, new Expr[]{u.get(0), u.get(1), u});
		if(u.length() == 1)
			s = Set.union(s, new Expr[]{u.get(0)});
		if(u.getOperator().equals(Operator.FDERIV) && !u.get(1).isList())
		{
			Expr f = u.get(0);
			Expr n = u.get(1);
			Expr a = u.get(2);
			if(n.isInt() && ((Int)n).isPositive())
			{
				Expr k = Simplification.simplify_recursive(new Expr(Operator.FDERIV, f, n.sub(Int.ONE), a));
				return Set.add(s, new Expr[]{k});
			}
		}
		if(u.getOperator().isFunction())
		    return Set.union(s, new Expr[]{u});
		return s;
	}

	public static Expr integrate_linear_properties(Expr u, Expr x) throws RecursionLimitReachedException
	{
		if(u.isProduct())
		{
			Expr[] cv = Simplification.constant_term(u, x);
			if(!cv[0].equals(Int.ONE))
			{
				Expr v = integrate_recursive(cv[1], x);
				if(!v.equals(Constant.FAIL))
					return cv[0].mul(v);
			}
		}
		if(u.isSum())
		{
			Expr s = Int.ZERO;
			for(int i = 0;i<u.length();i++)
			{
				Expr f = integrate_recursive(u.get(i), x);
				if(f.equals(Constant.FAIL))
					return Constant.FAIL;
				else
					s = s.add(f);
			}
			return s;
		}
		return Constant.FAIL;
	}

	public static Expr integrate_table(Expr u, Expr x) throws RecursionLimitReachedException 
	{
		if(u.isFreeOf(x))
			return u.mul(x);
		if(u.equals(x))
			return x.pow(Int.TWO).div(Int.TWO);
		if(u.isPower())
		{
			Expr b = u.get(0);
			Expr e = u.get(1);
			if(b.equals(x) && e.equals(Int.NONE))
				return new Expr(Operator.LOG, x);
			if(b.equals(x) && e.isFreeOf(x))
				return x.pow(e.add(Int.ONE)).div(e.add(Int.ONE));
			if(b.isFreeOf(x) && e.equals(x))
				return u.div(new Expr(Operator.LOG, b));
		}
		if(u.equals(new Expr(Operator.LOG, x)))
			return x.mul(new Expr(Operator.LOG, x)).sub(x);
		if(u.equals(new Expr(Operator.EXP, x)))
			return new Expr(Operator.EXP, x);
		if(u.equals(new Expr(Operator.SIN, x)))
			return new Expr(Operator.COS, x).mul(Int.NONE);
		if(u.equals(new Expr(Operator.COS, x)))
			return new Expr(Operator.SIN, x);
		if(u.equals(new Expr(Operator.TAN, x)))
			return new Expr(Operator.LOG, new Expr(Operator.COS, x)).mul(Int.NONE);
		
		Expr[] nd = Algebra.NumeratorDenominator(u);
		Expr p = nd[0];
		Expr q = nd[1];
		if(Poly.is_poly(p, x) && Poly.is_poly(q, x))
		{
			//Rational Quadratic
			Expr[] s = MatchForm.quadratic_form(q, x);
			if(s != null && p.equals(Int.ONE))
			{
				if(s[0].equals(Int.ZERO))
					return Constant.FAIL;
				Expr D = s[1].pow(Int.TWO).sub(Int.FOUR.mul(s[0].mul(s[2])));
				if(Simplification.is_positive(D))
				{
					Expr c = D.sqrt();
					Expr a = Int.TWO.mul(s[0].mul(x)).add(s[1]).div(c).artanh();
					return Algebra.expand(Int.NONE.mul(Int.TWO).mul(a).div(c));
				}
				if(D.equals(Int.ZERO))
				{
					return Algebra.cancel(Int.NONE.mul(Int.TWO).div(Int.TWO.mul(s[0].mul(x)).add(s[1])));
				}
				D = D.mul(Int.NONE);
				Expr c = D.sqrt();
				Expr a = new Expr(Operator.ARCTAN, Int.TWO.mul(s[0].mul(x)).add(s[1]).div(c));
				return Int.TWO.mul(a).div(c);
			}
			Expr[] r = MatchForm.linear_form(p, x);
			if(s!= null && r != null && !r[0].equals(Int.ZERO))
			{
				if(s[0].equals(Int.ZERO))
					return Constant.FAIL;
				Expr alpha = r[0].div(Int.TWO.mul(s[0]));
				Expr beta = r[1].sub(r[0].mul(s[1].div(Int.TWO.mul(s[0]))));
				Expr integral = integrate_recursive(Int.ONE.div(q), x);
				if(integral.equals(Constant.FAIL))
					return Constant.FAIL;
				return alpha.mul(new Expr(Operator.LOG, q)).add(beta.mul(integral));
			}
		}
		
		//Product of exponential and trigonometric
		Expr[] es = MatchForm.exp_sin_product(u, x);
		if(es != null && !es[0].equals(Int.ZERO) && !es[2].equals(Int.ZERO))
		{
			Expr w = Parser.build("exp(#a*#x+#b)*(#a*sin(#c*#x+#d)-#c*cos(#c*#x+#d))/(#a^2+#c^2)"
					, new String[]{"#x", "#a", "#b", "#c", "#d"}, new Expr[]{x, es[0], es[1], es[2], es[3]});
			return Algebra.expand(w);
		}
		es = MatchForm.exp_cos_product(u, x);
		if(es != null && !es[0].equals(Int.ZERO) && !es[2].equals(Int.ZERO))
		{
			Expr w = Parser.build("exp(#a*#x+#b)*(#a*cos(#c*#x+#d)+#c*sin(#c*#x+#d))/(#a^2+#c^2)"
					, new String[]{"#x", "#a", "#b", "#c", "#d"}, new Expr[]{x, es[0], es[1], es[2], es[3]});
			return Algebra.expand(w);
		}
		//sin(a*log(c*x+d)) and cos(a*log(c*x+d)+b)
		if(u.getOperator().equals(Operator.SIN))
		{
			Expr[] lf = MatchForm.linear_log_form(u.get(0), x);
			if(lf != null && !lf[2].equals(Int.ZERO))
			{
				Expr w = Parser.build("-((#c*#x+#d)*(#a*cos(#a*log(#c*#x+#d)+#b)-sin(#a*log(#c*#x+#d)+#b)))/((#a^2+1)*#c)"
						, new String[]{"#x", "#a", "#b", "#c", "#d"}, new Expr[]{x, lf[0], lf[1], lf[2], lf[3]});
				return w;
			}
		}
		if(u.getOperator().equals(Operator.COS))
		{
			Expr[] lf = MatchForm.linear_log_form(u.get(0), x);
			if(lf != null && !lf[2].equals(Int.ZERO))
			{
				Expr w = Parser.build("((#c*#x+#d)*(#a*sin(#a*log(#c*#x+#d)+#b)+cos(#a*log(#c*#x+#d)+#b)))/((#a^2+1)*#c)"
						, new String[]{"#x", "#a", "#b", "#c", "#d"}, new Expr[]{x, lf[0], lf[1], lf[2], lf[3]});
				return w;
			}
		}
		
		//Irrational
		if(u.isPower())
		{
			Expr[] qd = MatchForm.quadratic_form(u.get(0), x);
			if(qd != null && !qd[0].equals(Int.ZERO))
			{
				if(u.get(1).equals(Rational.HALF))
				{
					
				}
				if(u.get(1).equals(Rational.HALF.mul(Int.NONE)))
				{
					if(Simplification.is_negative(qd[0]))
					{
						Expr w = Parser.build("-1/sqrt(-#a)*arcsin((2*#a*#x+#b)/sqrt(#b^2-4*#a*#c))"
								, new String[]{"#x", "#a", "#b", "#c"}, new Expr[]{x, qd[0], qd[1], qd[2]});
						return w;
					}
					Expr w = Parser.build("1/sqrt(#a)*log(2*sqrt(#a)/#u+2*#a*#x+#b)"
							, new String[]{"#x", "#a", "#b", "#u"}, new Expr[]{x, qd[0], qd[1], u});
					return w;
				}
			}
		}
		
        return Constant.FAIL;	
	}
	
	public static Expr integrate_by_parts(Expr f, Expr x) throws RecursionLimitReachedException
	{
		if(f.isProduct())
		{
			if(f.length() == 2)
			{
				Expr A = f.get(0);
				Expr B = f.get(1);
				
				if(A.getOperator().equals(Operator.EXP) && Poly.is_poly(B, x))
					return by_parts(B, A, x);
				if(B.getOperator().equals(Operator.EXP) && Poly.is_poly(A, x))
					return by_parts(A, B, x);
				if(A.getOperator().equals(Operator.LOG) && Poly.is_poly(B, x))
					return by_parts(A, B, x);
				if(B.getOperator().equals(Operator.LOG) && Poly.is_poly(A, x))
					return by_parts(B, A, x);
				if(A.getOperator().equals(Operator.SIN) && Poly.is_poly(B, x))
					return by_parts(B, A, x);
				if(B.getOperator().equals(Operator.SIN) && Poly.is_poly(A, x))
					return by_parts(A, B, x);
				if(A.getOperator().equals(Operator.COS) && Poly.is_poly(B, x))
					return by_parts(B, A, x);
				if(B.getOperator().equals(Operator.COS) && Poly.is_poly(A, x))
					return by_parts(A, B, x);	
				if(A.isPower() && A.get(0).getOperator().equals(Operator.EXP) && Poly.is_poly(B, x))
					return by_parts(B, A, x);
				if(B.isPower() && B.get(0).getOperator().equals(Operator.EXP) && Poly.is_poly(A, x))
					return by_parts(A, B, x);
				if(A.getOperator().equals(Operator.ARCTAN) && Poly.is_poly(B, x))
					return by_parts(A, B, x);
				if(B.getOperator().equals(Operator.ARCTAN) && Poly.is_poly(A, x))
					return by_parts(B, A, x);
				if(A.getOperator().equals(Operator.ARCSIN) && Poly.is_poly(B, x))
					return by_parts(A, B, x);
				if(B.getOperator().equals(Operator.ARCSIN) && Poly.is_poly(A, x))
					return by_parts(B, A, x);
				if(A.getOperator().equals(Operator.ARCCOS) && Poly.is_poly(B, x))
					return by_parts(A, B, x);
				if(B.getOperator().equals(Operator.ARCCOS) && Poly.is_poly(A, x))
					return by_parts(B, A, x);
				
			}
			else
			{
				//Separate polynomial
				Expr v = Int.ONE;
				Expr p = Int.ONE;
				for(int i = 0;i<f.length();i++)
				{
					if(Poly.is_poly(f.get(i), x))
						p = Algebra.expand(p.mul(f.get(i)));
					else
					{
						if(f.get(i).getOperator().equals(Operator.EXP))
							v = v.mul(f.get(i));
						else if(f.get(i).getOperator().equals(Operator.LOG))
							v = v.mul(f.get(i));
						else if(f.get(i).getOperator().equals(Operator.SIN))
							v = v.mul(f.get(i));
						else if(f.get(i).getOperator().equals(Operator.COS))
							v = v.mul(f.get(i));
						else if(f.get(i).getOperator().equals(Operator.SINH))
							v = v.mul(f.get(i));
						else if(f.get(i).getOperator().equals(Operator.COSH))
							v = v.mul(f.get(i));
						else
							return Constant.FAIL;
					}
				}
				if(!p.isFreeOf(x) && !v.equals(Int.ONE))
					return Algebra.expand(by_parts(p, v, x));
			}
		}
		else
		{
			if(f.getOperator().equals(Operator.ARCTAN))
			{
				return by_parts(f, Int.ONE, x);
			}
			if(f.getOperator().equals(Operator.ARCSIN))
			{
				return by_parts(f, Int.ONE, x);
			}
			if(f.getOperator().equals(Operator.ARCCOS))
			{
				return by_parts(f, Int.ONE, x);
			}
			if(f.isPower())
			{
				Expr b = f.get(0);
				Expr e = f.get(1);
				if(b.equals(new Expr(Operator.LOG, x)))
				{
					if(e.isInt())
					{
						Int n = (Int)e;
						if(n.isPositive())
							return by_parts(f, Int.ONE, x);
					}
				}
			}
		}
		return Constant.FAIL;
	}
	
	private static Expr by_parts(Expr u, Expr dv, Expr x) throws RecursionLimitReachedException
	{
		Expr v = integrate_recursive(dv, x);
		if(v.equals(Constant.FAIL))
			return Constant.FAIL;
		Expr du = Diff.derivative(u, x);
		Expr integral = integrate_recursive(v.mul(du), x);
		if(integral.equals(Constant.FAIL))
			return Constant.FAIL;
		return u.mul(v).sub(integral);
	}
	
	public static Expr integrate_rational(Expr u, Expr x) throws RecursionLimitReachedException
	{
		u = Algebra.cancel(u);
		Expr[] nd = Algebra.NumeratorDenominator(u);
		Expr p = nd[0];
		Expr q = nd[1];
		if(!Poly.is_poly(p, x) || !Poly.is_poly(q, x))
			return Constant.FAIL;
		if(Poly.degree(p, x).compareTo(Poly.degree(q, x)) >= 0)
		{
			Expr[] qr = BasicPoly.polynomial_division(p, q, x);
			Expr proper = integrate_recursive(qr[1].div(q), x);
			Expr poly = integrate_recursive(qr[0], x);
			if(proper.equals(Constant.FAIL) || poly.equals(Constant.FAIL))
				return Constant.FAIL;
			return poly.add(proper);
		}
		Expr[][] f = Factor.factor_poly_rationals(q);
		if(f.length == 1 && (f[0].length == 1 || (f[0].length == 2 && f[0][0].isFreeOf(x))))
			return Constant.FAIL;
		Vector<Expr> l = new Vector<Expr>();
		Vector<Int> e = new Vector<Int>();
		for(int i = 0;i<f.length;i++)
		{
			for(int j = 0;j<f[i].length;j++)
			{
				l.add(f[i][j]);
				e.add(new Int(i+1));
			}
		}
		Expr[] w = l.toArray(new Expr[l.size()]);
		Expr[][] pf = Cancel.partial_fraction_3_cancel(p, w, e.toArray(new Int[e.size()]), x);
		Expr integral = Int.ZERO;
		for(int i = 0;i<pf.length;i++)
		{
			for(int j = 0;j<pf[i].length;j++)
			{
				Expr d = pf[i][j].div(w[i].pow(new Int(j+1)));
				if(Algebra.rationalize_expand(u.sub(d)).equals(Int.ZERO))
					return Constant.FAIL;
				Expr g = integrate_recursive(d, x);
				if(g.equals(Constant.FAIL))
					return Constant.FAIL;
				integral = integral.add(g);
			}
		}
		return integral;
	}
	
	
}
