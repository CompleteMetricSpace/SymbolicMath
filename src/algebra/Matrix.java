package algebra;

import java.util.Vector;

import polynomial.Factor;
import polynomial.Poly;
import solve.LinearAlgebra;
import solve.PolySolve;
import Expression.Expr;
import Expression.SingularMatrixException;
import Simplification.*;
import Symbolic.Int;
import Symbolic.Numerical;

public class Matrix
{
	
	public static Expr[][] add(Expr[][] A, Expr[][] B)
	{
		if(A.length != B.length)
			throw new IllegalArgumentException("Matrices do not have same dimensions");
		Expr[][] C = new Expr[A.length][];
		for(int i = 0;i<C.length;i++)
		{
			if(A[i].length != B[i].length)
				throw new IllegalArgumentException("Matrices do not have same dimensions");
			C[i] = new Expr[A[i].length];
			for(int j = 0;j<C[i].length;j++)
				C[i][j] = A[i][j].add(B[i][j]);
		}
		return C;
	}
	
	public static Expr[][] sub(Expr[][] A, Expr[][] B)
	{
		return add(A, multiply_scalar(Int.NONE, B));
	}
	
	
	public static boolean isZero(Expr[][] A)
	{
	    for(int i = 0;i<A.length;i++)
	    {
	    	for(int j = 0;j<A[i].length;j++)
	    	{
	    		if(!A[i][j].equals(Int.ZERO))
	    			return false; 
	    	}
	    }
	    return true;
	}
	
	
    public static Expr[][] copy(Expr[][] M)
    {
    	Expr[][] B = new Expr[M.length][];
    	for(int i = 0;i<B.length;i++)
    	{
    		B[i] = new Expr[M[i].length];
    		for(int j = 0;j<B[i].length;j++)
    			B[i][j] = M[i][j];
    	}
    	return B;
    }
    
    public static Expr[][] row_echelon(Expr[][] A, int k, boolean reduce)
    {
    	Expr[][] B = copy(A);
    	int j = 0, t = 0;
    	while(j < k && t<B.length)
    	{
    		//Find pivot
    		int i;
    		boolean pivot_found = false;
    		for(i = t;i<B.length;i++)
    		{
                if(!B[i][j].equals(Int.ZERO))
                {
                	pivot_found = true;
                	break;
                }
    		}
    		if(!pivot_found)
    		{
    			j = j+1;
    			continue;
    		}
    		else
    		{
    			if(i != t)
    			{
    				//Switch rows i and t
    				Expr[] tmp = new Expr[B[i].length];
    				for(int f = 0;f<tmp.length;f++)
    					tmp[f] = B[i][f];
    				for(int f = 0;f<B[t].length;f++)
    					B[i][f] = B[t][f];
    				for(int f = 0;f<tmp.length;f++)
    					B[t][f] = tmp[f];
    			}
    			Expr pivot = B[t][j];
    			//perform elimination
    			for(int f = t+1;f<B.length;f++)
    			{
    				Expr q = Algebra.cancel(B[f][j].div(pivot));
    				for(int g = j;g<B[f].length;g++)
    					B[f][g] = Algebra.cancel(B[f][g].sub(q.mul(B[t][g])));
    			}
    			//Reduced row echelon
    			//Find non-zero pivot
    			if(reduce && j < k-1)
    			{
    				pivot_found = false;
    				int h;
    				for(h = B.length-1;h>t;h--)
    				{
    					if(!B[h][j+1].equals(Int.ZERO))
    					{
    						pivot_found = true;
    						break;
    					}
    				}
    				if(pivot_found)
    				{
    					pivot = B[h][j+1];
    					//eliminate
    					for(int f = h-1;f>=0;f--)
    					{
    						Expr q = Algebra.cancel(B[f][j+1].div(pivot));
    						for(int g = j+1;g<B[f].length;g++)
    							B[f][g] = Algebra.cancel(B[f][g].sub(q.mul(B[h][g])));
    					}
    				}
    			}
    			if(reduce)
    			{
    				
    				//make leading element 1
					for(int g = 0;g<k;g++)
					{
						if(!B[t][g].equals(Int.ZERO))
						{
							Expr d = B[t][g];
							for(int h = g;h<B[t].length;h++)
								B[t][h] = Algebra.cancel(B[t][h].div(d));
							break;
						}
					}
    			}
    			j = j+1;
    	        t = t+1;
    		}
    	}
    	return B;
    }
    
    public static Expr[][] inverse_matrix(Expr[][] A)
    {
       	Expr[][] id = identity_matrix(A.length);
       	Expr[][] C = append(A, id);
       	Expr[][] B = row_echelon(C, A.length, true);
       	Expr[][] I = cut_columns(B, 0, A[0].length);
       	if(!equal(I, id))
       		throw new SingularMatrixException("Cannot invert matrix");
       	return cut_columns(B, A[0].length, B[0].length);
    }

	public static Expr[][] append(Expr[][] A, Expr[][] B)
	{
		Expr[][] C = new Expr[A.length][];
		for(int i = 0;i<C.length;i++)
		{
			int n = A[i].length, m = B[i].length;
			C[i] = new Expr[n+m];
			for(int j = 0;j<n;j++)
				C[i][j] = A[i][j];
			for(int j = n;j<n+m;j++)
				C[i][j] = B[i][j-n];
		}
		return C;
	}
	
	private static Expr[][] cut_columns(Expr[][] A, int k, int l)
	{
		int n = l-k;
		Expr[][] B = new Expr[A.length][];
		for(int i = 0;i<B.length;i++)
		{
			B[i] = new Expr[n];
			for(int j = k;j<l;j++)
				B[i][j-k] = A[i][j];
		}
		return B;
	}

	public static Expr[][] identity_matrix(int n) 
	{
		Expr[][] B = new Expr[n][n];
		for(int i = 0;i<n;i++)
		{
			for(int j = 0;j<n;j++)
			{
				if(i == j)
					B[i][j] = Int.ONE;
				else
					B[i][j] = Int.ZERO;
			}
		}
		return B;
	}
	
	public static boolean equal(Expr[][] A, Expr[][] B)
	{
	    if(A.length != B.length)
	    	return false;
	    for(int i = 0;i<A.length;i++)
	    {
	    	if(A[i].length != B[i].length)
	    		return false;
	    	for(int j = 0;j<A[i].length;j++)
	    	{
	    		if(!A[i][j].equals(B[i][j]))
	    			return false;
	    	}
	    }
	    return true;
	}
	
	public static Expr determinant(Expr[][] A)
	{
		if(A[0].length != A.length)
			throw new IllegalArgumentException("matrix is not a square matrix");
		Expr det = LinearAlgebra.fraction_free_elimination(A)[1][0][0];
		return det;
	}
	
	public static Expr determinant_laplace(Expr[][] A)
	{
		if(A[0].length != A.length)
			throw new IllegalArgumentException("matrix is not a square matrix");
		if(A.length == 1)
			return A[0][0];
		if(A.length == 2)
			return A[0][0].mul(A[1][1]).sub(A[1][0].mul(A[0][1]));
		Expr det = Int.ZERO;
		for(int i = 0;i<A[0].length;i++)
		{
			Expr a = A[0][i];
			if(a.equals(Int.ZERO))
				continue;
			else
				det = Algebra.cancel(det.add(a.mul(cofactor(A, 0, i))));
		}
		return det;
	}

	private static Expr cofactor(Expr[][] A, int i, int j) 
	{
		return Int.NONE.pow(new Int((j+1)+(i+1))).mul(minor(A, i, j));
	}

	private static Expr minor(Expr[][] A, int i, int j) 
	{
		return determinant_laplace(submatrix(A, i, j));
	}

	public static Expr[][] submatrix(Expr[][] A, int r, int c) 
	{
		Expr[][] B = new Expr[A.length-1][];
		for(int i = 0;i<A.length;i++)
		{
			if(i<r)
			{
				B[i] = new Expr[A[i].length-1];
				for(int j = 0;j<A[i].length;j++)
				{
					if(j<c)
						B[i][j] = A[i][j];
					if(j>c)
						B[i][j-1] = A[i][j];
				}
			}
			else if(i>r)
			{
				B[i-1] = new Expr[A[i].length-1];
				for(int j = 0;j<A[i].length;j++)
				{
					if(j<c)
						B[i-1][j] = A[i][j];
					if(j>c)
						B[i-1][j-1] = A[i][j];
				}
			}
		}
		return B;
	}
	
	public static Expr[][] cofactor_matrix(Expr[][] A)
	{
		Expr[][] C = new Expr[A.length][];
		for(int i = 0;i<C.length;i++)
		{
			C[i] = new Expr[A[i].length];
			for(int j = 0;j<C[i].length;j++)
				C[i][j] = cofactor(A, i, j);
		}
		return C;
	}
	
	public static Expr[][] inverse_matrix_laplace(Expr[][] A)
	{
		Expr det = determinant_laplace(A);
		if(det.equals(Int.ZERO))
			throw new SingularMatrixException("Cannot invert matrix");
		Expr[][] C = cofactor_matrix(A);
		return multiply_scalar(Int.ONE.div(det), transpose(C));
	}

	public static Expr[][] multiply_scalar(Expr a, Expr[][] A) 
	{
		Expr[][] C = new Expr[A.length][];
		for(int i = 0;i<C.length;i++)
		{
			C[i] = new Expr[A[i].length];
			for(int j = 0;j<C[i].length;j++)
				C[i][j] = Algebra.cancel(A[i][j].mul(a));
		}
		return C;
	}
	
	public static Expr[][] transpose(Expr[][] A)
	{
		if(A.length == 0)
			return A;
		Expr[][] C = new Expr[A[0].length][];
		for(int i = 0;i<C.length;i++)
		{
			C[i] = new Expr[A.length];
			for(int j = 0;j<C[i].length;j++)
				C[i][j] = A[j][i];
		}
		return C;
	}
	
	public static Expr[][] multiply(Expr[][] A, Expr[][] B)
	{
		if(A[0].length != B.length)
			throw new IllegalArgumentException("matrix dimension error");
		Expr[][] C = new Expr[A.length][B[0].length];
		for(int i = 0;i<C.length;i++)
		{
			for(int j = 0;j<C[i].length;j++)
			{
				Expr p = Int.ZERO;
				for(int k = 0;k<A[0].length;k++)
					p = p.add(A[i][k].mul(B[k][j]));
				C[i][j] = p;
			}
		}
		return C;
	}
	
	public static Expr[][] inverse(Expr[][] A)
	{
		return inverse_matrix(A);
	}
	
	public static Expr[][] power(Expr[][] A, Int n)
	{
		if(n.isNegative())
			return power(inverse(A), n.mul(Int.NONE));
		if(n.equals(Int.ZERO))
			return identity_matrix(A.length);
		if(n.equals(Int.ONE))
			return A;
		if(n.isOdd())
			return multiply(A, power(multiply(A, A), n.sub(Int.ONE).divide(Int.TWO)));
		else
			return power(multiply(A, A), n.divide(Int.TWO));
	}

    /*
     * Kochrezept 6.2-7 LA I/II Skript Dipper
     * Returns matrix A and vector b in 6.2-7-form and a set of 
     * column permutations used to obtain this form
     */
	public static Expr[][][] kochrezept(Expr[][] B, Expr[] b)
	{
	    Vector<Int[]> change_column = new Vector();
		Expr[][] A = copy(B);
		if(isZero(A))
			return new Expr[][][]{A, new Expr[][]{b},
				new Int[][]{}};
		boolean done = false;
		int c = 0, r = 0;
		while(!done)
		{
			boolean found_nonzero = false;
			outloop:
			for(int i = c;i<A[0].length;i++)
			{
				for(int j = r;j<A.length;j++)
				{
					if(!A[j][i].equals(Int.ZERO))
					{
						found_nonzero = true;
						if(j != r)
						{
							//Change rows j and r:
							for(int k = 0;k<A[0].length;k++)
							{
								Expr tmp = A[j][k];
								A[j][k] = A[r][k];
								A[r][k] = tmp;
							}
							//Change b also
							Expr tmp = b[j];
							b[j] = b[r];
							b[r] = tmp;
						}
						if(i != c)
						{
							//Change columns i and c:
                            change_column.add(new Int[]{new Int(i), new Int(c)});
                            for(int k = 0;k<A.length;k++)
							{
								Expr tmp = A[k][i];
								A[k][i] = A[k][c];
								A[k][c] = tmp;
							}
						}
						//Now, there is some nonzero element in A[r][c], divide the whole row by it
						Expr d = A[r][c];
						for(int k = 0;k<A[r].length;k++)
							A[r][k] = Algebra.cancel(A[r][k].div(d));
						b[r] = Algebra.cancel(b[r].div(d));
						//A[r][c] = 1 by now
						//Now remove any elements under row r in column c
						for(int k = r+1;k<A.length;k++)
						{
						    d = A[k][c];
							for(int l = c;l<A[k].length;l++)
								A[k][l] = Algebra.cancel(A[k][l].sub(A[r][l].mul(d)));
							b[k] = Algebra.cancel(b[k].sub(b[r].mul(d)));
						}
						//Go outside both for loops
						break outloop;
					}
				}
			
			}
			if(found_nonzero)
			{
				r++;
				c++;
				continue;
			}
			else
			{
				done = true;
			}
		}
		//Make entries above 1-Diagonal equal 0
		for(int i = 0;i<Integer.min(A.length, A[0].length);i++)
		{
			if(A[i][i].equals(Int.ZERO))
				break;
			for(int j = 0;j<i;j++)
			{
				Expr e = A[j][i];
				for(int l = i;l<A[0].length;l++)
				{
					A[j][l] = A[j][l].sub(e.mul(A[i][l]));
				}
				b[j] = b[j].sub(e.mul(b[i]));
			}
		}
		return new Expr[][][]{A,new Expr[][]{b},
				change_column.toArray(new Int[change_column.size()][])};
	}
	
	public static Expr char_polynomial(Expr[][] M, Expr u)
	{
		if(!is_square_matrix(M))
			throw new IllegalArgumentException("M is not a square matrix");
		return Algebra.expand(Algebra.cancel(Matrix.determinant(sub(M, multiply_scalar(u, identity_matrix(M.length))))));
	}

	//Works only if M is a matrix
	public static boolean is_square_matrix(Expr[][] M)
	{
		return M[0].length == M.length;
	}
	
	public static boolean is_matrix(Expr[][] M)
	{
		int n = M[0].length;
		for(int i = 0;i<M.length;i++)
		{
			if(M[i].length != n)
				return false;
		}
		return true;
	}
	
	public static Expr[][] jordan_form(Expr[][] M)
	{
		Expr t = Simplification.getNewVariables(1, Set.toList(M))[0];
		Expr p = char_polynomial(M, t);
		Expr[][] f = Factor.factor_poly_rationals(p);
		Expr[][] jordan_form = new Expr[][]{};
		//Solve for eigenvalues
		for(int i = 0;i<f.length;i++)
		{
			Expr[] d = f[i];
			for(int j = 0;j<d.length;j++)
			{
				if(d[j].isFreeOf(t))
					continue;
				if(Poly.degree(d[j], t).compareTo(Int.TWO) > 0)
					throw new IllegalArgumentException("Cannot solve for eigenvalues: "+d[j]);
				Expr[] s = PolySolve.solve_irreducible_polynomial_Q(d[j], t);
				for(int k = 0;k<s.length;k++)
				{
					Int[] jord = jordan_blocks(M, s[k]);
					for(int l = 0;l<jord.length;l++)
						jordan_form = Set.add(jordan_form, new Expr[][]{{s[k], jord[l]}});
				}
			}
		}
		return jordan_form;
	}
	
	/*
	 * 
	 * @param M - a quadratic matrix
	 * @param a - an eigenvalue of M
	 * @return list [k_1,...,k_r] where k_i is the number of jordan blocks of size i
	 */
	public static Int[] jordan_blocks(Expr[][] M, Expr a)
	{
		int n = M.length;
		Vector<Int> l = new Vector<Int>();
		Int prev_dim = Int.NONE;
		Expr[][] L = sub(M, multiply_scalar(a, identity_matrix(n)));
		Expr[][] D = copy(L);
		while(true)
		{
			Int k = LinearAlgebra.get_dimension_of_kernel(D);
			if(k.equals(prev_dim))
				break;
			l.add(k);
			D = multiply(D, L);
			prev_dim = k;
		}
		Vector<Int> h = new Vector<Int>();
		h.add(l.get(0));
		for(int i = 1;i<l.size();i++)
		    h.add(l.get(i).sub(l.get(i-1)));
		Vector<Int> k = new Vector<Int>();
		k.add(h.lastElement());
		for(int i = h.size()-2;i>=0;i--)
		    k.add(0, h.get(i).sub(h.get(i+1)));
		Vector<Int> s = new Vector<Int>();
		for(int i = 0;i<k.size();i++)
		{
			for(Int j = Int.ZERO;j.compareTo(k.get(i))<0;j = j.add(Int.ONE))
				s.add(new Int(i+1));
		}
		return s.toArray(new Int[s.size()]);
	}
	
	public static Expr[][] jordan_basis(Expr[][] M)
	{
		Expr t = Simplification.getNewVariables(1, Set.toList(M))[0];
		Expr p = char_polynomial(M, t);
		Expr[][] f = Factor.factor_poly_rationals(p);
		Expr[][] jordan_basis = new Expr[][]{};
		//Solve for eigenvalues
		for(int i = 0;i<f.length;i++)
		{
			Expr[] d = f[i];
			for(int j = 0;j<d.length;j++)
			{
				if(d[j].isFreeOf(t))
					continue;
				if(Poly.degree(d[j], t).compareTo(Int.TWO) > 0)
					throw new IllegalArgumentException("Cannot solve for eigenvalues: "+d[j]);
				Expr[] s = PolySolve.solve_irreducible_polynomial_Q(d[j], t);
				for(int k = 0;k<s.length;k++)
				{
					Expr[][] jord = jordan_block_basis(M, s[k]);
					jordan_basis = Set.add(jordan_basis, jord);
				}
			}
		}
		return jordan_basis;
	}
	
	public static Expr[][] jordan_block_basis(Expr[][] M, Expr a)
	{
		Expr[][] basis = new Expr[][]{};
		Vector<Expr[][]> basis_vec = new Vector<Expr[][]>();
		int n = M.length;
		Expr[] zero = Set.toExprArray(Int.ZERO, n);
		Int prev_dim = Int.NONE;
		Expr[][] L = sub(M, multiply_scalar(a, identity_matrix(n)));
		Expr[][] D = copy(L);
		while(true)
		{
			System.out.println("D: "+Expr.toString(D));
			Expr[][] bs = LinearAlgebra.get_basis_solution_space(D, zero)[0];
			System.out.println("bs: "+bs.length);
			if(new Int(bs.length).equals(prev_dim))
				break;
			if(basis.length == 0)
			{
				basis = copy(bs);
				basis_vec.add(bs);
			}
			else
			{
				System.out.println("bs: "+Expr.toString(bs));
				System.out.println("basis: "+Expr.toString(basis));
				Expr[][] comp = LinearAlgebra.complete_basis(basis, bs, bs.length-basis.length);
				System.out.println("comp: "+Expr.toString(comp));
				basis = Set.add(basis, comp);
				basis_vec.add(comp);
			}
			D = multiply(D, L);
			prev_dim = new Int(bs.length);
		}
		System.out.println("basis: "+Expr.toString(basis));
		Vector<Expr[][]> jordan = new Vector<Expr[][]>();
		jordan.add(basis_vec.lastElement());
		for(int i = basis_vec.size()-1;i >= 1;i--)
		{
			Expr[][] s = new Expr[jordan.get(0).length][];
			for(int j = 0;j<s.length;j++)
				s[j] = column_matrix_to_vector(multiply(L, to_column_matrix(jordan.get(0)[j])));
			Expr[][] comp = LinearAlgebra.complete_basis(s, basis_vec.get(i-1), basis_vec.get(i-1).length-s.length);
			s = Set.add(s, comp);
			jordan.add(0, s);
		}
		Vector<Expr[]> final_basis = new Vector<Expr[]>();
		int index = 0;
		for(int i = jordan.size()-1;i>=0;i--)
		{
			for(int j = index;j<jordan.get(i).length;j++)
			{
			    for(int k = 0;k<=i;k++)
			    	final_basis.add(jordan.get(k)[j]);
			}
			index = jordan.get(i).length;
		}
		return final_basis.toArray(new Expr[final_basis.size()][]);
	}
	
	public static Expr[][] to_column_matrix(Expr[] u)
	{
		Expr[][] m = new Expr[u.length][1];
		for(int i = 0;i<m.length;i++)
			m[i][0] = u[i];
		return m;
	}
	
	public static Expr[] column_matrix_to_vector(Expr[][] m)
	{
		Expr[] u = new Expr[m.length];
		for(int i = 0;i<u.length;i++)
			u[i] = m[i][0];
		return u;
	}
	
	
	
}

