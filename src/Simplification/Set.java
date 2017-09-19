package Simplification;
import java.util.Vector;

import Expression.Expr;
import Expression.Operator;
import Symbolic.Int;
import Symbolic.Numerical;


public class Set
{

	public static int indexOf(Expr[] list, Expr e)
	{
		for(int i = 0;i<list.length;i++)
			if(list[i].equals(e))
				return i;
		return -1;
	}
	
	public static Expr[] add(Expr[] s, Expr[] b)
	{
		Expr[] n = new Expr[s.length+b.length];
		for(int i = 0;i<s.length;i++)
			n[i] = s[i];
		for(int i = 0;i<b.length;i++)
			n[i+s.length] = b[i];
		return n;
	}
	
	public static Numerical[] add(Numerical[] a, Numerical[] b)
	{
		Numerical[] n = new Numerical[a.length+b.length];
		for(int i = 0;i<a.length;i++)
			n[i] = a[i];
		for(int i = 0;i<b.length;i++)
			n[i+a.length] = b[i];
		return n;
	}
	
	public static Expr[][] add(Expr[][] a, Expr[][] b)
	{
		Expr[][] n = new Expr[a.length+b.length][];
		for(int i = 0;i<a.length;i++)
			n[i] = a[i];
		for(int i = 0;i<b.length;i++)
			n[i+a.length] = b[i];
		return n;
	}
	
	public static Numerical[][] add(Numerical[][] a, Numerical[][] b)
	{
		Numerical[][] n = new Numerical[a.length+b.length][];
		for(int i = 0;i<a.length;i++)
			n[i] = a[i];
		for(int i = 0;i<b.length;i++)
			n[i+a.length] = b[i];
		return n;
	}
	
	public static Expr[] remove_dublicates(Expr[] a)
	{
		Vector<Expr> e = new Vector<>();
		for(int i = 0;i<a.length;i++)
		{
			boolean has = false;
			for(int j = 0;j<e.size();j++)
			{
				if(e.get(j).equals(a[i]))
					has= true;
			}
			if(!has)
				e.add(a[i]);
		}
		return e.toArray(new Expr[e.size()]);
	}
	
	public static Expr[] substitute(Expr[] a, Expr b, Expr c)
	{
		Expr[] n = new Expr[a.length];
		for(int i = 0;i<n.length;i++)
		{
			if(a[i].equals(b))
				n[i] = c;
			else
				n[i] = a[i];
		}
		return n;
	}
	
	public static Expr[] remove(Expr[] a, int index)
	{
		Expr[] n = new Expr[a.length-1];
		for(int i = 0;i<a.length;i++)
		{
			if(i<index)
				n[i] = a[i];
			if(i>index)
				n[i-1] = a[i];
		}
		return n;
	}
	
	public static Expr[][] remove(Expr[][] a, int index)
	{
		Expr[][] n = new Expr[a.length-1][];
		for(int i = 0;i<a.length;i++)
		{
			if(i<index)
				n[i] = a[i];
			if(i>index)
				n[i-1] = a[i];
		}
		return n;
	}
	
	public static Expr[] rest(Expr[] a)
	{
		Expr[] n = new Expr[a.length-1];
		for(int i = 1;i<a.length;i++)
		{
			n[i-1] = a[i];
		}
		return n;
	}
	
	public static Int[] rest(Int[] a)
	{
		Int[] n = new Int[a.length-1];
		for(int i = 1;i<a.length;i++)
		{
			n[i-1] = a[i];
		}
		return n;
	}
	
	public static Expr[][] rest(Expr[][] a)
	{
		Expr[][] n = new Expr[a.length-1][];
		for(int i = 1;i<a.length;i++)
		{
			n[i-1] = a[i];
		}
		return n;
	}
	
	public static Numerical[][] rest(Numerical[][] a)
	{
		Numerical[][] n = new Numerical[a.length-1][];
		for(int i = 1;i<a.length;i++)
		{
			n[i-1] = a[i];
		}
		return n;
	}
	
	public static Expr[] first(Expr[] a)
	{
		Expr[] n = new Expr[a.length-1];
		for(int i = 0;i<a.length-1;i++)
		{
			n[i] = a[i];
		}
		return n;
	}
	
	public static Int[] first(Int[] a)
	{
		Int[] n = new Int[a.length-1];
		for(int i = 0;i<a.length-1;i++)
		{
			n[i] = a[i];
		}
		return n;
	}
	
	public static Expr last(Expr[] a)
	{
		return a[a.length-1];
	}
	
	public static Expr[] set(Expr[] a, int index, Expr b)
	{
		Expr[] n = new Expr[a.length+1];
		for(int i = 0;i<index;i++)
		{
			n[i] = a[i];
		}
		n[index] = b;
		for(int i = index+1;i<n.length;i++)
			n[i] = a[i-1];
		return n;
	}
	
	public static boolean member(Expr[] vars, Expr u)
	{
		for(int i = 0;i<vars.length;i++)
		{
			if(u.equals(vars[i]))
				return true;
		}
		return false;
	}
	
	public static boolean member(Expr[][] vars, Expr[] u)
	{
		for(int i = 0;i<vars.length;i++)
		{
			if(equal(vars[i], u))
				return true;
		}
		return false;
	}
	
	public static boolean member(Int[][] vars, Int[] u)
	{
		for(int i = 0;i<vars.length;i++)
		{
			if(equal(u, vars[i]))
				return true;
		}
		return false;
	}
	
	public static Expr[] union(Expr[] a, Expr[] b)
	{
		Vector<Expr> vec = new Vector();
		for(int i = 0;i<a.length;i++)
		{
			if(!Set.member(vec.toArray(new Expr[vec.size()]), a[i]))
				vec.add(a[i]);
		}
		for(int i = 0;i<b.length;i++)
		{
			if(!Set.member(vec.toArray(new Expr[vec.size()]), b[i]))
				vec.add(b[i]);
		}
		return vec.toArray(new Expr[vec.size()]);
	}
	
	public static Expr[][] union(Expr[][] a, Expr[][] b)
	{
		Vector<Expr[]> vec = new Vector();
		for(int i = 0;i<a.length;i++)
		{
			if(!Set.member(vec.toArray(new Expr[vec.size()][]), a[i]))
				vec.add(a[i]);
		}
		for(int i = 0;i<b.length;i++)
		{
			if(!Set.member(vec.toArray(new Expr[vec.size()][]), b[i]))
				vec.add(b[i]);
		}
		return vec.toArray(new Expr[vec.size()][]);
	}
	
	public static Int[] union(Int[] a, Int[] b)
	{
		Vector<Int> vec = new Vector();
		for(int i = 0;i<a.length;i++)
		{
			if(!Set.member(vec.toArray(new Int[vec.size()]), a[i]))
				vec.add(a[i]);
		}
		for(int i = 0;i<b.length;i++)
		{
			if(!Set.member(vec.toArray(new Int[vec.size()]), b[i]))
				vec.add(b[i]);
		}
		return vec.toArray(new Int[vec.size()]);
	}
	
	public static Int[][] union(Int[][] a, Int[][] b)
	{
		Vector<Int[]> vec = new Vector();
		for(int i = 0;i<a.length;i++)
		{
			if(!Set.member(vec.toArray(new Int[vec.size()][]), a[i]))
				vec.add(a[i]);
		}
		for(int i = 0;i<b.length;i++)
		{
			if(!Set.member(vec.toArray(new Int[vec.size()][]), b[i]))
				vec.add(b[i]);
		}
		return vec.toArray(new Int[vec.size()][]);
	}
	
	public static Expr[] intersect(Expr[] a, Expr[] b)
	{
		Vector<Expr> vec = new Vector();
		for(int i = 0;i<a.length;i++)
		{
			if(member(b, a[i]))
				vec.add(a[i]);
		}
		return vec.toArray(new Expr[vec.size()]);
		
	}
	
	public static Expr[] union(Expr[][] a) 
	{
		if(a.length == 1)
			return a[0];
		if(a.length == 2)
			return union(a[0], a[1]);
		Expr[][] b = new Expr[a.length-1][];
		for(int i = 0;i<b.length;i++)
			b[i] = a[i+1];
		Expr[] un = union(b);
		return union(a[0], un);
	}
	
	public static boolean equal(Expr[] a, Expr[] b)
	{
		if(a.length != b.length)
			return false;
		for(int i = 0;i<a.length;i++)
		{
			if(!a[i].equals(b[i]))
				return false;
		}
		return true;
	}
	
	public static String toString(Expr[] a)
	{
		if(a.length == 0)
			return "[]";
		String s = "["+a[0];
		for(int i = 1;i<a.length;i++)
			s += ","+a[i];
		return s+"]";
	}

	public static Expr[] addElementwise(Expr[] exprs, Int[] m) 
	{
		Expr[] a = new Expr[m.length];
		for(int i = 0;i<a.length;i++)
			a[i] = exprs[i].add(m[i]);
		return a;
	}

	public static boolean is_in_vector(Vector<Int> q, Int b) 
	{
		for(int i = 0;i<q.size();i++)
		{
			if(q.get(i).equals(b))
				return true;
		}
		return false;
	}
	
	public static Expr[][] subsets(Expr[] s)
	{
		if(s.length == 0)
			return new Expr[][]{{}};
		Expr a = s[0];
		Expr[] R = Set.rest(s);
		Expr[][] b = subsets(R);
		Expr[][] c = new Expr[b.length][];
		for(int i = 0;i<c.length;i++)
		{
			c[i] = add(new Expr[]{a}, b[i]); 
		}
		return add(c, b);
	}
	
	public static Expr[][] subsets(Expr[] s, int m)
	{
		if(s.length == m)
			return new Expr[][]{s};
		if(m == 0)
			return new Expr[][]{{}};
		Expr x = s[0];
		Expr[] T = complement(s, new Expr[]{x});
		Expr[][] D = subsets(T, m-1);
		Expr[][] E = new Expr[D.length][];
		for(int i = 0;i<E.length;i++)
			E[i] = union(D[i], new Expr[]{x});
		return union(E, subsets(T, m));
	}

	public static Expr[] complement(Expr[] a, Expr[] b) 
	{
		Vector<Expr> vec = new Vector();
		for(int i = 0;i<a.length;i++)
		{
			if(!member(b, a[i]))
				vec.add(a[i]);
		}
		return vec.toArray(new Expr[vec.size()]);
	}
	
	public static Expr[][] complement(Expr[][] a, Expr[][] b) 
	{
		Vector<Expr[]> vec = new Vector();
		for(int i = 0;i<a.length;i++)
		{
			if(!member(b, a[i]))
				vec.add(a[i]);
		}
		return vec.toArray(new Expr[vec.size()][]);
	}

	public static Expr[][] clean_up(Expr[][] c, Expr[] t)
	{
		Vector<Expr[]> n = new Vector<>();
		for(int i = 0;i<c.length;i++)
		{
			if(Expr.isFreeOf(c[i], t))
				n.add(c[i]);
		}
		return n.toArray(new Expr[n.size()][]);
	}

	public static Int[] exprToIntArray(Expr[] list)
	{
		Int[] n = new Int[list.length];
		for(int i = 0;i<list.length;i++)
		{
			if(list[i].isInt())
				n[i] = (Int)list[i];
			else
				return null;
		}
		return n;
	}

	public static Expr toList(Expr[] s)
	{
	    Expr[] k = new Expr[s.length];
	    for(int i = 0;i<s.length;i++)
	    	k[i] = s[i];
	    return new Expr(Operator.LIST, k);
	}
	
	public static Expr toList(Expr[][] s)
	{
		 Expr[] k = new Expr[s.length];
		 for(int i = 0;i<s.length;i++)
		    	k[i] = toList(s[i]);
		 return new Expr(Operator.LIST, k);
	}
	

	public static Expr[][] toExprArray(Expr list)
	{
		Expr[][] C = new Expr[list.length()][];
		for(int i = 0;i<C.length;i++)
		{
			Expr a = list.get(i);
			C[i] = new Expr[a.length()];
			for(int j = 0;j<C[i].length;j++)
				C[i][j] = a.get(j);
		}
		return C;
	}

	public static Expr[] toExprArray(Expr a, int n)
	{
		Expr[] c = new Expr[n];
		for(int i = 0;i<n;i++)
			c[i] = a;
		return c;
	}
	
	public static Expr[][] toExprArrayColumn(Expr a, int n)
	{
		Expr[][] c = new Expr[n][1];
		for(int i = 0;i<n;i++)
			c[i][0] = a;
		return c;
	}
	
	public static Expr[][] flatten(Expr[][][] u)
	{
		Vector<Expr[]> v = new Vector<Expr[]>();
		for(int i = 0;i<u.length;i++)
			for(int j = 0;j<u[i].length;j++)
				v.add(u[i][j]);
		return v.toArray(new Expr[v.size()][]);
	}
}
