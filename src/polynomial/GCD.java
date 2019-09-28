package polynomial;

import java.util.Vector;

import algebra.Algebra;
import Expression.Expr;
import Simplification.Set;
import Simplification.Simplification;
import Symbolic.Constant;
import Symbolic.Int;
import Symbolic.Numerical;

public class GCD
{
    static Constant DEFAULT_GCD = Constant.MODULAR;

    public static Expr multivariate_gcd(Expr u, Expr v, String K)
    {
	Expr[] vars = Set.union(Poly.variables(u), Poly.variables(v));
	if(vars.length == 0)
	    return Int.ONE;
	Expr[] subs = Simplification.getNewVariables(vars.length, u, v);
	u = u.substitute(vars, subs);
	v = v.substitute(vars, subs);
	Expr gcd = multivariate_gcd(u, v, subs, K);
	return Simplification.simplify_recursive(gcd.substitute(subs, vars));
    }

    public static Expr multivariate_gcd(Expr[] u, String K)
    {
	Expr[] vars = new Expr[] {};
	for(int i = 0; i < u.length; i++)
	    vars = Set.union(vars, Poly.variables(u[i]));
	if(vars.length == 0)
	    return Int.ONE;
	Expr[] subs = Simplification.getNewVariables(vars.length, u);
	Expr[] s = new Expr[u.length];
	for(int i = 0; i < s.length; i++)
	    s[i] = u[i].substitute(vars, subs);
	Expr gcd = multivariate_gcd(s, subs, K, DEFAULT_GCD);
	return Simplification.simplify_recursive(gcd.substitute(subs, vars));
    }

    public static Expr multivariate_gcd(Expr u, Expr v, Expr[] L, String K)
    {
	return multivariate_gcd(u, v, L, K, gcd_method(u, v, L));
    }

    public static Expr multivariate_gcd(Expr u, Expr v, Expr[] L, String K, Constant c)
    {
	if(K.equals("Z"))
	{
	    if(c.equals(Constant.EUCLID))
		return multivariate_euclid_gcd(u, v, L, "Z");
	    if(c.equals(Constant.SUBRESULTANT))
		return multivariate_gcd_sr(u, v, L, "Z");
	    if(c.equals(Constant.MODULAR))
		return modular_gcd_integers(u, v, L);
	}
	else
	{
	    if(c.equals(Constant.EUCLID))
		return multivariate_euclid_gcd(u, v, L, "Q");
	    if(c.equals(Constant.SUBRESULTANT))
		return multivariate_gcd_sr(u, v, L, "Q");
	    if(c.equals(Constant.MODULAR))
		return modular_gcd_rationals(u, v, L);
	}
	return null;
    }

    public static Expr multivariate_gcd(Expr[] u, Expr[] L, String K, Constant c)
    {
	if(u.length == 1)
	    return normalize_gcd(u[0], L, K);
	if(u.length == 2)
	    return multivariate_gcd(u[0], u[1], L, K, c);
	Int[] k = new Int[u.length - 1];
	for(int i = 0; i < k.length; i++)
	    k[i] = Int.random_int(new Int("-1000000"), new Int("1000000"));
	Expr F = u[0];
	for(int i = 2; i < u.length; i += 2)
	    F = Algebra.expand(F.add(k[i - 1].mul(u[i])));
	Expr G = u[1];
	for(int i = 1; i < u.length; i += 2)
	    G = Algebra.expand(G.add(k[i - 1].mul(u[i])));
	Expr Hp = multivariate_gcd(F, G, L, K, c);
	Expr[] s = new Expr[] {};
	for(int i = 0; i < u.length; i++)
	{
	    if(!BasicPoly.multivariate_division(u[i], Hp, L, K)[1].equals(Int.ZERO))
		s = Set.add(s, new Expr[] {u[i]});
	}
	s = Set.union(s, new Expr[] {Hp});
	if(s.length > 1)
	    return multivariate_gcd(s, L, K, c);
	return s[0];
    }

    public static Expr content(Expr u, Expr x, Expr[] R, String K)
    {
	return content(u, x, R, K, DEFAULT_GCD);
    }

    public static Expr primitive(Expr u, Expr x)
    {
	Expr[] vars = Set.complement(Poly.variables(u), new Expr[] {x});
	Expr[] subs = Simplification.getNewVariables(vars.length, u, x);
	u = u.substitute(vars, subs);
	Expr pp = primitive(u, x, subs, "Q");
	return pp.substitute(subs, vars);
    }

    public static Expr primitive(Expr u, Expr x, Expr[] R, String K)
    {
	Expr cont = content(u, x, R, K);
	return BasicPoly.multivariate_division(u, cont, Set.add(new Expr[] {x}, R), K)[0];
    }

    public static Expr content(Expr u, Expr x, Expr[] R, String K, Constant method)
    {
	Int n = Poly.degree(u, x);
	Expr gcd = null;
	for(Int i = Int.ZERO; i.compareTo(n) <= 0; i = i.add(Int.ONE))
	{

	    Expr c = Poly.coefficient_poly(u, x, i);
	    if(i.equals(Int.ZERO))
		gcd = c;
	    else
		gcd = multivariate_gcd(gcd, c, R, K, method);
	    if(gcd.equals(Int.ONE))
		return Int.ONE;
	}
	return gcd;
    }

    public static Expr polynomial_gcd(Expr u, Expr v, Expr x)
    {
	if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
	    return Int.ZERO;
	Expr U = u;
	Expr V = v;
	while(!V.equals(Int.ZERO))
	{
	    Expr R = BasicPoly.polynomial_remainder(U, V, x);
	    U = V;
	    V = R;
	}
	return BasicPoly.make_monic(U, x);
    }

    public static Expr polynomial_gcd_p(Expr u, Expr v, Expr x, Int p)
    {
	u = FiniteField.to_non_negative(u, p);
	v = FiniteField.to_non_negative(v, p);
	if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
	    return Int.ZERO;
	Expr U = u;
	Expr V = v;
	while(!V.equals(Int.ZERO))
	{
	    Expr R = BasicPoly.polynomial_remainder_p(U, V, x, p);
	    U = V;
	    V = R;
	}
	Int lc = (Int) Poly.leading_coef_Q(U, x);
	return FiniteField.to_non_negative(lc.modInverse(p).mul(U), p);
    }

    public static Expr[] polynomial_extended_gcd(Expr u, Expr v, Expr x)
    {
	if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
	    return new Expr[] {Int.ZERO, Int.ZERO, Int.ZERO};
	Expr U = u;
	Expr V = v;
	Expr App = Int.ONE;
	Expr Ap = Int.ZERO;
	Expr Bpp = Int.ZERO;
	Expr Bp = Int.ONE;
	while(!V.equals(Int.ZERO))
	{
	    Expr[] qr = BasicPoly.polynomial_division(U, V, x);
	    Expr q = qr[0];
	    Expr r = qr[1];
	    Expr A = App.sub(q.mul(Ap));
	    Expr B = Bpp.sub(q.mul(Bp));
	    App = Ap;
	    Ap = A;
	    Bpp = Bp;
	    Bp = B;
	    U = V;
	    V = r;
	}
	Expr c = Poly.leading_coef(U, x);
	App = Algebra.expand(App.div(c));
	Bpp = Algebra.expand(Bpp.div(c));
	U = Algebra.expand(U.div(c));
	return new Expr[] {U, App, Bpp};
    }

    public static Expr[] polynomial_extended_gcd(Expr[] u, Expr x)
    {
	if(u.length == 1)
	    return new Expr[] {u[0], Int.ONE};
	if(u.length == 2)
	    return polynomial_extended_gcd(u[0], u[1], x);
	Expr u_1 = u[0];
	Expr[] u_r = Set.rest(u);
	Expr[] gcd_u_r = polynomial_extended_gcd(u_r, x);
	Expr[] bc = polynomial_extended_gcd(u_1, gcd_u_r[0], x);
	Expr[] ext = new Expr[u.length + 1];
	ext[0] = bc[0];
	ext[1] = bc[1];
	for(int i = 2; i < ext.length; i++)
	    ext[i] = Algebra.expand(gcd_u_r[i - 1].mul(bc[2]));
	return ext;
    }

    public static Expr[] polynomial_extended_gcd_p(Expr u, Expr v, Expr x, Int p)
    {
	u = FiniteField.to_non_negative(u, p);
	v = FiniteField.to_non_negative(v, p);
	if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
	    return new Expr[] {Int.ZERO, Int.ZERO, Int.ZERO};
	Expr U = u;
	Expr V = v;
	Expr App = Int.ONE;
	Expr Ap = Int.ZERO;
	Expr Bpp = Int.ZERO;
	Expr Bp = Int.ONE;
	while(!V.equals(Int.ZERO))
	{
	    Expr[] qr = BasicPoly.polynomial_division_p(U, V, x, p);
	    Expr q = qr[0];
	    Expr r = qr[1];
	    Expr A = App.sub(q.mul(Ap));
	    Expr B = Bpp.sub(q.mul(Bp));
	    App = Ap;
	    Ap = A;
	    Bpp = Bp;
	    Bp = B;
	    U = V;
	    V = r;
	}
	Int c = (Int) Poly.leading_coef_Q(U, x);
	Int c_i = c.modInverse(p);
	App = Algebra.expand(FiniteField.to_non_negative(App.mul(c_i), p));
	Bpp = Algebra.expand(FiniteField.to_non_negative(Bpp.mul(c_i), p));
	U = Algebra.expand(FiniteField.to_non_negative(U.mul(c_i), p));
	return new Expr[] {U, App, Bpp};
    }

    public static Expr[] polynomial_extended_gcd_p(Expr[] u, Expr x, Int p)
    {
	if(u.length == 1)
	    return new Expr[] {u[0], Int.ONE};
	if(u.length == 2)
	    return polynomial_extended_gcd_p(u[0], u[1], x, p);
	Expr u_1 = u[0];
	Expr[] u_r = Set.rest(u);
	Expr[] gcd_u_r = polynomial_extended_gcd_p(u_r, x, p);
	Expr[] bc = polynomial_extended_gcd_p(u_1, gcd_u_r[0], x, p);
	Expr[] ext = new Expr[u.length + 1];
	ext[0] = bc[0];
	ext[1] = bc[1];
	for(int i = 2; i < ext.length; i++)
	    ext[i] = Algebra.expand(FiniteField.to_non_negative(gcd_u_r[i - 1].mul(bc[2]), p));
	return ext;
    }

    public static Int integer_content(Expr u, Expr[] L)
    {
	if(L.length == 0)
	    return (Int) u;
	if(u.equals(Int.ZERO))
	    return Int.ZERO;
	Expr x = L[0];
	Expr[] R = Set.rest(L);
	Int n = Poly.degree(u, x);
	Int gcd = null;
	for(Int i = Int.ZERO; i.compareTo(n) <= 0; i = i.add(Int.ONE))
	{
	    Int c = integer_content(Poly.coefficient_poly(u, x, i), R);
	    if(i.equals(Int.ZERO))
		gcd = c;
	    else
		gcd = Int.gcd(gcd, c);
	    if(gcd.equals(Int.ONE))
		return Int.ONE;
	}
	return gcd;
    }

    public static Expr content_p(Expr u, Expr[] L, Expr[] R, Int p)
    {
	if(L.length == 0)
	    return u;
	if(u.equals(Int.ZERO))
	    return Int.ZERO;
	Expr x = L[0];
	Expr[] rest = Set.rest(L);
	Int n = Poly.degree(u, x);
	Expr gcd = null;
	for(Int i = Int.ZERO; i.compareTo(n) <= 0; i = i.add(Int.ONE))
	{
	    Expr coef = Poly.coefficient_poly(u, x, i);
	    Expr c = content_p(coef, rest, R, p);
	    if(i.equals(Int.ZERO))
		gcd = c;
	    else
		gcd = modular_gcd_reduction(gcd, c, R, p);
	    if(gcd.equals(Int.ONE))
		return Int.ONE;
	}
	return gcd;
    }

    public static Expr modular_gcd_rationals(Expr u, Expr v, Expr[] L)
    {
	Int a = Poly.coefficient_lcm(u, L);
	Int b = Poly.coefficient_lcm(v, L);
	u = u.mul(a);
	v = v.mul(b);
	Expr gcd = modular_gcd_integers(u, v, L);
	gcd = normalize_gcd(gcd, L, "Q");
	return gcd;
    }

    public static Expr modular_gcd_integers(Expr u, Expr v, Expr[] L)
    {
	if(u.isInt() && v.isInt())
	    return Int.gcd((Int) u, (Int) v);
	if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
	    return Int.ZERO;
	Int a = integer_content(u, L);
	Int b = integer_content(v, L);
	Expr A = u.div(a);
	Expr B = v.div(b);
	Int c = Int.gcd(a, b);
	if(u.equals(Int.ZERO))
	    return v.div(b).mul(c);
	if(v.equals(Int.ZERO))
	    return u.div(a).mul(c);
	Expr lc_A = Poly.leading_coef(A, L);
	Expr lc_B = Poly.leading_coef(B, L);
	Int g = Int.gcd((Int) lc_A, (Int) lc_B);
	Int q = Int.ONE;
	Expr H = Int.ZERO;
	Expr x = L[0];
	Int n = Int.min(Poly.degree(A, x), Poly.degree(B, x));
	Int limit = (Int) Int.TWO.pow(n).mul(g.abs())
		.mul(Int.min(Poly.poly_height(A, L), Poly.poly_height(b, L)));
	Int p_k = new Int("18446744073709551616");
	while(true)
	{
	    Int p = Int.find_prime(p_k);
	    while(g.mod(p).isZero())
		p = Int.find_prime(p.add(Int.ONE));
	    p_k = p.add(Int.ONE);
	    Expr Ap = FiniteField.to_non_negative(A, p);
	    Expr Bp = FiniteField.to_non_negative(B, p);
	    Int gp = g.mod(p);
	    Expr Cp = modular_gcd_reduction(Ap, Bp, L, p);
	    Int m = Poly.degree(Cp, x);
	    Int lc_Cp = (Int) Poly.leading_coef(Cp, L);
	    Cp = FiniteField.to_non_negative(gp.mul(lc_Cp.modInverse(p)).mul(Cp), p);
	    if(m.compareTo(n) < 0)
	    {
		q = p;
		H = Cp;
		n = m;
	    }
	    else if(m.equals(n) || (m.equals(Int.NONE) && n.isZero())
		    || (n.equals(Int.NONE) && m.isZero()))
	    {
		Expr new_H = FiniteField.integer_chinese_remainder_garner(new Expr[] {H, Cp},
			new Int[] {q, p});
		q = q.mul(p);
		if(q.compareTo(limit) > 0 || new_H.equals(H))
		{
		    Expr C = new_H.div(integer_content(new_H, L));
		    Expr r_A = BasicPoly.multivariate_division(A, C, L, "Z")[1];
		    Expr r_B = BasicPoly.multivariate_division(B, C, L, "Z")[1];
		    if(r_A.equals(Int.ZERO) && r_B.equals(Int.ZERO))
			return c.mul(C);
		}
		H = new_H;
		if(m.compareTo(Int.ZERO) <= 0)
		    return c;
	    }
	}
    }

    public static Expr modular_gcd_p(Expr[] A, Expr[] L, Int p)
    {
	if(A.length == 1)
	    return FiniteField.to_non_negative(A[0], p);
	if(A.length == 2)
	    return modular_gcd_reduction(A[0], A[1], L, p);
	Expr[] B = Set.rest(A);
	Expr gcd = modular_gcd_p(B, L, p);
	return modular_gcd_reduction(A[0], gcd, L, p);
    }

    public static Expr modular_gcd_reduction(Expr A, Expr B, Expr[] L, Int p)
    {
	if(A.equals(Int.ZERO))
	    return B;
	if(B.equals(Int.ZERO))
	    return A;
	if(L.length == 1)
	{
	    Expr C = polynomial_gcd_p(A, B, L[0], p);
	    if(Poly.degree(C, L[0]).compareTo(Int.ZERO) <= 0)
		return Int.ONE;
	    return C;
	}
	Expr x = L[0];
	Expr[] R = Set.rest(L);
	// Speed up
	if(A.isFreeOf(x) && B.isFreeOf(x))
	    return modular_gcd_reduction(A, B, R, p);
	Expr a = content_p(A, R, new Expr[] {x}, p);
	Expr b = content_p(B, R, new Expr[] {x}, p);
	A = BasicPoly.multivariate_division_p(A, a, L, p)[0];
	B = BasicPoly.multivariate_division_p(B, b, L, p)[0];
	Expr c = polynomial_gcd_p(a, b, x, p);
	Expr lc_A = Poly.leading_coef(A, R);
	Expr lc_B = Poly.leading_coef(B, R);
	Expr g = polynomial_gcd_p(lc_A, lc_B, x, p);
	Vector<Int> q = new Vector<Int>();
	Vector<Expr> H = new Vector<Expr>();
	Int n = Int.min(Poly.degree(A, x), Poly.degree(B, x));
	while(true)
	{
	    Int bb = null;
	    do
	    {
		bb = Int.random_int(Int.ZERO, p);
	    }
	    while(Simplification.simplify_recursive(g.substitute(x, bb)).equals(Int.ZERO)
		    || Set.is_in_vector(q, bb));
	    Expr Ab = Simplification.simplify_recursive(A.substitute(x, bb));
	    Expr Bb = Simplification.simplify_recursive(B.substitute(x, bb));
	    Expr Cb = modular_gcd_reduction(Ab, Bb, R, p);
	    Int m = Poly.degree(Cb, R[0]);
	    Int gb = (Int) Simplification.simplify_recursive(g.substitute(x, bb));
	    Int lc_Cb = (Int) Poly.leading_coef(Cb, L);
	    Cb = FiniteField.to_non_negative(gb.mul(lc_Cb.modInverse(p)).mul(Cb), p);
	    if(m.equals(n) || (m.equals(Int.NONE) && n.isZero())
		    || (n.equals(Int.NONE) && m.isZero()))
	    {
		q.add(bb);
		H.add(Cb);
		Expr C = FiniteField.newton_interpolation(q.toArray(new Int[q.size()]),
			H.toArray(new Expr[H.size()]), x, p);
		C = FiniteField.to_non_negative(C, p);
		Expr Cg = FiniteField.to_non_negative(Poly.leading_coef(C, R).sub(g), p);
		if(Cg.equals(Int.ZERO))
		{
		    Expr ppC = content_p(C, R, new Expr[] {x}, p);
		    C = BasicPoly.multivariate_division_p(C, ppC, L, p)[0];
		    Expr r_A = BasicPoly.multivariate_division_p(A, C, L, p)[1];
		    Expr r_B = BasicPoly.multivariate_division_p(B, C, L, p)[1];
		    if(r_A.equals(Int.ZERO) && r_B.equals(Int.ZERO))
			return FiniteField.to_non_negative(Algebra.expand(c.mul(C)), p);
		}
	    }
	    else
	    {
		q.clear();
		H.clear();
		n = m;
	    }
	}
    }

    public static Expr multivariate_euclid_gcd(Expr u, Expr v, Expr[] L, String K)
    {
	if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
	    return Int.ZERO;
	if(u.equals(Int.ZERO))
	    return normalize_gcd(v, L, K);
	if(v.equals(Int.ZERO))
	    return normalize_gcd(u, L, K);
	return normalize_gcd(mv_euclid_rec(u, v, L, K), L, K);
    }

    private static Expr mv_euclid_rec(Expr u, Expr v, Expr[] L, String K)
    {
	if(L.length == 0)
	{
	    if(K.equals("Z"))
	    {
		return Int.gcd((Int) u, (Int) v);
	    }
	    else
	    {
		return Int.ONE;
	    }
	}
	else
	{
	    Expr x = L[0];
	    Expr[] R = Set.rest(L);
	    Expr cont_u = content(u, x, R, K, Constant.EUCLID);
	    Expr cont_v = content(v, x, R, K, Constant.EUCLID);
	    Expr d = mv_euclid_rec(cont_u, cont_v, R, K);
	    Expr pp_u = BasicPoly.multivariate_division(u, cont_u, L, K)[0];
	    Expr pp_v = BasicPoly.multivariate_division(v, cont_v, L, K)[0];
	    while(!pp_v.equals(Int.ZERO))
	    {
		Expr r = BasicPoly.pseudo_division(pp_u, pp_v, x)[1];
		Expr pp_r;
		if(r.equals(Int.ZERO))
		    pp_r = Int.ZERO;
		else
		{
		    Expr cont_r = content(r, x, R, K, Constant.EUCLID);
		    pp_r = BasicPoly.multivariate_division(r, cont_r, L, K)[0];
		}
		pp_u = pp_v;
		pp_v = pp_r;
	    }
	    return Algebra.expand(d.mul(pp_u));
	}
    }

    private static Expr normalize_gcd(Expr u, Expr[] L, String K)
    {
	if(K.equals("Z"))
	{
	    Int lcu = (Int) Poly.leading_coef(u, L);
	    if(lcu.isNegative())
		return Algebra.expand(Int.NONE.mul(u));
	    return u;
	}
	else
	{
	    Numerical lcu = (Numerical) Poly.leading_coef(u, L);
	    return Algebra.expand(u.div(lcu));
	}
    }

    public static Expr multivariate_gcd_sr(Expr u, Expr v, Expr[] L, String K)
    {
	if(u.equals(Int.ZERO) && v.equals(Int.ZERO))
	    return Int.ZERO;
	if(u.equals(Int.ZERO))
	    return normalize_gcd(v, L, K);
	if(v.equals(Int.ZERO))
	    return normalize_gcd(u, L, K);
	return normalize_gcd(mv_subresultant_rec(u, v, L, K), L, K);
    }

    private static Expr mv_subresultant_rec(Expr u, Expr v, Expr[] L, String K)
    {
	if(L.length == 0)
	{
	    if(K.equals("Z"))
		return Int.gcd((Int) u, (Int) v);
	    else
		return Int.ONE;
	}
	else
	{
	    Expr x = L[0];
	    Expr U, V;
	    if(Poly.degree(u, x).compareTo(Poly.degree(v, x)) >= 0)
	    {
		U = u;
		V = v;
	    }
	    else
	    {
		U = v;
		V = u;
	    }
	    Expr[] R = Set.rest(L);
	    Expr cont_U = content(U, x, R, K, Constant.SUBRESULTANT);
	    Expr cont_V = content(V, x, R, K, Constant.SUBRESULTANT);
	    Expr d = multivariate_gcd_sr(cont_U, cont_V, R, K);
	    U = BasicPoly.multivariate_division(U, cont_U, L, K)[0];
	    V = BasicPoly.multivariate_division(V, cont_V, L, K)[0];
	    Expr g = multivariate_gcd_sr(Poly.leading_coef(U, x), Poly.leading_coef(V, x), R, K);
	    Int i = Int.ONE;
	    Int delta = Int.ZERO;
	    Expr beta = Int.ZERO;
	    Expr psi = Int.ZERO;
	    while(!V.equals(Int.ZERO))
	    {
		Expr r = BasicPoly.pseudo_division(U, V, x)[1];
		if(!r.equals(Int.ZERO))
		{
		    if(i.equals(Int.ONE))
		    {
			delta = Poly.degree(U, x).sub(Poly.degree(V, x)).add(Int.ONE);
			psi = Int.NONE;
			beta = Int.NONE.pow(delta);
		    }
		    else if(i.compareTo(Int.ONE) > 0)
		    {
			Int delta_p = delta;
			delta = Poly.degree(U, x).sub(Poly.degree(V, x)).add(Int.ONE);
			Expr f = Poly.leading_coef(U, x);
			Expr t_1 = Algebra.expand(Int.NONE.mul(f).pow(delta_p.sub(Int.ONE)));
			Expr t_2 = Algebra.expand(psi.pow(delta_p.sub(Int.TWO)));
			psi = BasicPoly.multivariate_division(t_1, t_2, L, K)[0];
			beta = Algebra.expand(Int.NONE.mul(f).mul(psi.pow(delta.sub(Int.ONE))));
		    }
		    U = V;
		    V = BasicPoly.multivariate_division(r, beta, L, K)[0];
		    i = i.add(Int.ONE);
		}
		else
		{
		    U = V;
		    V = r;
		}
	    }
	    Expr s = BasicPoly.multivariate_division(Poly.leading_coef(U, x), g, R, K)[0];
	    Expr W = BasicPoly.multivariate_division(U, s, L, K)[0];
	    Expr cont_W = content(W, x, R, K, Constant.SUBRESULTANT);
	    Expr pp_W = BasicPoly.multivariate_division(W, cont_W, L, K)[0];
	    return Algebra.expand(d.mul(pp_W));
	}
    }

    public static Expr[] solve(Expr a, Expr b, Expr c, Expr x)
    {
	Expr[] gst = polynomial_extended_gcd(a, b, x);
	Expr s = gst[1], t = gst[2], g = gst[0];
	Expr[] qr = BasicPoly.polynomial_division(c, g, x);
	Expr q = qr[0], r = qr[1];
	if(!r.equals(Int.ZERO))
	    return null;
	s = Algebra.expand(q.mul(s));
	t = Algebra.expand(q.mul(t));
	if(!s.equals(Int.ZERO) && Poly.degree(s, x).compareTo(Poly.degree(b, x)) >= 0)
	{
	    qr = BasicPoly.polynomial_division(s, b, x);
	    q = qr[0];
	    r = qr[1];
	    s = r;
	    t = Algebra.expand(t.add(q.mul(a)));
	}
	return new Expr[] {s, t};
    }

    public static Constant gcd_method(Expr u, Expr v, Expr[] L)
    {
	if(L.length > 3)
	    return Constant.SUBRESULTANT;
	
	return Constant.MODULAR;
    }

    public static Expr multivariate_gcd_anf(Expr[] ps, Expr[] vars,
	    Expr[] exprs, Expr[] exprs2)
    {
	// TODO Auto-generated method stub
	return null;
    }
}
