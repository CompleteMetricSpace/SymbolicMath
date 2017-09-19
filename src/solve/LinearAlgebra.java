package solve;

import algebra.Algebra;
import algebra.Matrix;
import polynomial.BasicPoly;
import Expression.Expr;
import Simplification.Set;
import Symbolic.Constant;
import Symbolic.Int;

public class LinearAlgebra 
{
	public static Expr[] solve_system(Expr[][] A, Expr[] b)
	{
		int n = A[0].length;
		Expr[][] M = new Expr[A.length][n+1];
		for(int i = 0;i<A.length;i++)
			for(int j = 0;j<A[i].length+1;j++)
			{
				if(j < A[i].length)
				    M[i][j] = A[i][j];
				else
					M[i][j] = b[i];
			}
 		Expr[][][][] F = fraction_free_elimination_list(M);
 		Expr[][] N = new Expr[A.length][A[0].length];
 		for(int i = 0;i<A.length;i++)
			for(int j = 0;j<A[i].length;j++)
			    N[i][j] = F[0][n][i][j];
 		Int rank_A = rank_elimit(N);
 		Int rank_M = rank_elimit(F[0][n]);
 		if(!rank_A.equals(rank_M))
 			return null; //inconsistent
		if(n == rank_A.toInt())
		{
			Expr[] X = back_solve(F[0][n], n);
			return X;
		}
 		return back_solve_underdetermined(F[0][n], rank_A.toInt(), n); //underdetermined
	}
	
	//Does NOT compute the rank, but does count number of zero rows
	public static Int rank_elimit(Expr[][] A)
	{
		Int r = Int.ZERO;
		for(int i = 0;i<A.length;i++)
		{
			boolean zero_row = true;
			for(int j = 0;j<A[i].length;j++)
				if(!A[i][j].equals(Int.ZERO))
					zero_row = false;
			if(!zero_row)
				r = r.add(Int.ONE);
		}
		return r;
	}

	public static Expr[][][][] fraction_free_elimination_list(Expr[][] B)
	{
		Expr[][] A = Matrix.copy(B);
		Int sign = Int.ONE;
		Expr divisor = Int.ONE;
		int r = 1;
		int m = A.length;
		int n = A[0].length;
		Expr[][][] A_ = new Expr[n][m][n];
		for(int i = 0;i<A.length;i++)
			for(int j = 0;j<A[i].length;j++)
				A_[0][i][j] = A[i][j];
		int k;
		for(k = 1;k<=n && r<=m;k++)
		{
			int p;
			for(p = r;p<=m && A[p-1][k-1].equals(Int.ZERO);p++);
			if(p<=m)
			{
				for(int j = k;j<=n;j++)
				{
					Expr tmp = A[p-1][j-1];
					A[p-1][j-1] = A[r-1][j-1];
					A[r-1][j-1] = tmp;
				}
				if(r != p)
					sign = sign.mul(Int.NONE);
				for(int i = r+1;i<=m;i++)
				{
					for(int j = k+1;j<=n;j++)
					{
						A[i-1][j-1] = Algebra.cancel(A[r-1][k-1].mul(A[i-1][j-1])
								.sub(A[r-1][j-1].mul(A[i-1][k-1])).div(divisor));
					}
					A[i-1][k-1] = Int.ZERO;
				}
				divisor = A[r-1][k-1];
				r = r + 1;
			}
			for(int i = 0;i<A.length;i++)
				for(int j = 0;j<A[i].length;j++)
					A_[k-1][i][j] = A[i][j];
		}
		Expr det = Int.ZERO;
		if(r == m+1)
			det = sign.mul(divisor);
		//fill A_
		while(k<=n-1)
		{
			for(int i = 0;i<A.length;i++)
				for(int j = 0;j<A[i].length;j++)
					A_[k][i][j] = A[i][j];
			k++;
		}
		return new Expr[][][][]{A_, {{{det}}}};
	}
	
	public static Expr[][][] fraction_free_elimination(Expr[][] B)
	{
		Expr[][] A = Matrix.copy(B);
		int m = A.length, n = A[0].length;
		int sign = 1;
		Expr divisor = Int.ONE;
		int r = 1;
		for(int k = 1;k<=n && r<=m;k++)
		{
			int p;
			for(p = r;p<=m && A[p-1][k-1].equals(Int.ZERO);p++);
			if(p<=m)
			{
				for(int j = k;j<=n;j++)
				{
					Expr tmp = A[p-1][j-1];
					A[p-1][j-1] = A[r-1][j-1];
					A[r-1][j-1] = tmp;
				}
				if(r != p)
					sign = -sign;
				for(int i = r+1;i<=m;i++)
				{
					for(int j = k+1;j<=n;j++)
					{
						A[i-1][j-1] = Algebra.cancel(A[r-1][k-1].mul(A[i-1][j-1])
								.sub(A[r-1][j-1].mul(A[i-1][k-1])).div(divisor));
					}
					A[i-1][k-1] = Int.ZERO;
				}
				divisor = A[r-1][k-1];
				r = r + 1;
			}

		}
		Expr det;
		if(r == m+1)
			det = new Int(sign).mul(divisor);
		else
			det = Int.ZERO;
		return new Expr[][][]{A, {{det}}};
	}
	
	public static Expr[] back_solve_fraction_free(Expr[][][] A, int n)
	{
		Expr[] x = new Expr[n];
		x[n-1] = A[n-1][n-1][n+1-1];
		for(int k = n-1;k>=1;k--)
		{
			Expr sum = Int.ZERO;
			for(int j = k+1;j<=n;j++)
			{
				sum = sum.add(A[k-1][k-1][j-1].mul(x[j-1]));
			}
			x[k-1] = A[n-1][n-1][n-1].mul(A[k-1][k-1][n+1-1]).sub(sum).div(A[k-1][k-1][k-1]);
		}
		return x;
	}
	
	public static Expr[] back_solve(Expr[][] A, int n)
	{
		Expr[] x = new Expr[n];
		x[n-1] = A[n-1][n].div(A[n-1][n-1]);
		for(int k = n-1;k>=1;k--)
		{
			Expr sum = Int.ZERO;
			for(int j = k+1;j<=n;j++)
			{
				sum = sum.add(A[k-1][j-1].mul(x[j-1]));
			}
			x[k-1] = A[k-1][n].sub(sum).div(A[k-1][k-1]);
		}
		return x;
	}
	
	public static Expr[] back_solve_underdetermined(Expr[][] A, int n, int vars)
	{
		//Check for zero columns
		int it;
		for(it = 0;it<A[0].length;it++)
		{
			boolean is_zero = true;
			for(int j = 0;j<A.length;j++)
			{
				if(!A[j][it].equals(Int.ZERO))
					is_zero = false;
			}
			if(is_zero)
				break;
		}
		if(it<A[0].length-1)
		{
			Expr[][] B = new Expr[A.length+1][A[0].length-1];
			Expr[] C = new Expr[A.length+1];
			for(int k = 0;k<A.length;k++)
			{
				for(int j = 0;j<A[k].length-1;j++)
					B[k][j] = A[k][j];
				C[k] = A[k][A[0].length-1];
			}
			for(int j = 0;j<A[0].length-1;j++)
			{
				if(j == it)
					B[B.length-1][j] = Int.ONE;
				else
					B[B.length-1][j] = Int.ZERO;
			}
			C[A.length] = Int.ZERO;
			return solve_system(B, C);
		}
		
		Expr[] x = new Expr[vars];
		for(int k = n;k>=1;k--)
		{
			//Search for first nonzero element;
			int j;
			for(j = 1;j<=A[k-1].length && A[k-1][j-1].equals(Int.ZERO);j++);
			//Fill undefined variables
			for(int i = j+1;i<=vars;i++)
			    if(x[i-1] == null)
			    	x[i-1] = Int.ZERO;
			Expr sum = Int.ZERO;
			for(int i = j+1;i<=vars;i++)
				sum = sum.add(A[k-1][i-1].mul(x[i-1]));
			x[j-1] = A[k-1][vars].sub(sum).div(A[k-1][j-1]);
		}
		return x;
	}
	
	/*
	 * Returns a list [[x_1,...,x_n],[b_n]] such that the solution space is 
	 * S = {a_1*x_1 + ... + a_n*x_n + b_n | a_1,...,a_n in K}.
	 * Returns an empty list [] if there is no solution.
	 */
	public static Expr[][][] get_basis_solution_space(Expr[][] A, Expr[] b)
	{
		Expr[][][] C = Matrix.kochrezept(A, b);
		A = C[0];
		b = C[1][0];
		Expr[][] ch = C[2]; 
		int r = Integer.min(A.length, A[0].length);
		for(int i = 0;i<Integer.min(A.length, A[0].length);i++)
		{
			if(A[i][i].equals(Int.ZERO))
			{
				r = i;
				break;
			}
		}
		//No Solution
		for(int i = r;i<b.length;i++)
			if(!b[i].equals(Int.ZERO))
			{
				return new Expr[][][]{}; 
			}
		Expr[][] S = new Expr[][]{};
		for(int i = r;i<A[0].length;i++)
		{
			Expr[] x = new Expr[A[0].length];
			for(int j = 0;j <= r-1;j++)
				x[j] = Int.NONE.mul(A[j][i]);
			for(int j = r;j < x.length;j++)
			{
				if(j == i)
					x[j] = Int.ONE;
				else
					x[j] = Int.ZERO;
			}
		    S = Set.add(S, new Expr[][]{x});
		}
		Expr[] b_new = new Expr[A[0].length];
		for(int i = 0;i<b.length;i++)
			b_new[i] = b[i];
		for(int i = b.length;i<b_new.length;i++)
			b_new[i] = Int.ZERO;
		//Change variables back:
		while(ch.length != 0)
		{
			int g = ((Int)ch[ch.length-1][0]).toInt();	
			int h = ((Int)ch[ch.length-1][1]).toInt();
			ch = Set.remove(ch, ch.length-1);
			for(int i = 0;i<S.length;i++)
			{
				Expr tmp = S[i][g];
				S[i][g] = S[i][h];
				S[i][h] = tmp;
			}
			Expr tmp = b_new[g];
			b_new[g] = b_new[h];
			b_new[h] = tmp;
		}
		return new Expr[][][]{S,new Expr[][]{b_new}};
	}
	
	public static boolean is_in_span(Expr[][] B, Expr[] b)
	{
		Expr[][] A = Matrix.transpose(B);
		int n = A[0].length;
		Expr[][] M = new Expr[A.length][n+1];
		for(int i = 0;i<A.length;i++)
			for(int j = 0;j<A[i].length+1;j++)
			{
				if(j < A[i].length)
				    M[i][j] = A[i][j];
				else
					M[i][j] = b[i];
			}
 		Expr[][] F = fraction_free_elimination(M)[0];
 		Expr[][] N = new Expr[A.length][A[0].length];
 		for(int i = 0;i<A.length;i++)
			for(int j = 0;j<A[i].length;j++)
			    N[i][j] = F[i][j];
 		Int rank_A = rank_elimit(N);
 		Int rank_M = rank_elimit(F);
 		if(!rank_A.equals(rank_M))
 		    return false;
 		else
 			return true;
	}
	
	public static Expr[][] complete_basis(Expr[][] B, Expr[][] C, int n)
	{
		Expr[][] E = new Expr[][]{};
		int k = 0, i = 0;
		while(k < n && i<C.length)
		{
			if(is_in_span(B, C[i]))
			{
				System.out.println("in span: "+Expr.toString(C[i]));
				System.out.println("B: "+Expr.toString(B));
			    i++;
			}
			else
			{
				B = Set.add(B, new Expr[][]{C[i]});
				E = Set.add(E, new Expr[][]{C[i]});
				i++;
				k++;
			}
		}
		if(E.length<n)
			throw new IllegalArgumentException("Couldn't add "+n+" lin. independent vectors to set B from C");
		else
			return E;
	}
	
	public static Int get_dimension_of_kernel(Expr[][] M)
	{
		M = fraction_free_elimination(M)[0];
		return new Int(M[0].length).sub(rank_elimit(M));
	}
}
