package Symbolic;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.security.SecureRandom;
import java.util.LinkedList;
import java.util.Vector;

import Expression.Expr;
import Simplification.Set;

public class Int extends Numerical
{

    BigInteger integer;

    public static Int ONE = new Int("1");
    public static Int NONE = new Int("-1");
    public static Int ZERO = new Int("0");
    public static Int TWO = new Int("2");
    public static Int THREE = new Int("3");
    public static Int FOUR = new Int("4");
    public static Int FIVE = new Int("5");
    public static Int SIX = new Int("6");
    public static Int EIGHT = new Int("8");
    public static Int TEN = new Int("10");

    public Int(String s)
    {
	integer = new BigInteger(s);
    }

    public Int(BigInteger s)
    {
	integer = s;
    }

    public Int(int s)
    {
	integer = BigInteger.valueOf(s);
    }
    
    public Int(long s)
    {
	integer = BigInteger.valueOf(s);
    }

    public BigInteger toBigInteger()
    {
	return integer;
    }

    public BigDecimal toBigDecimal()
    {
	return new BigDecimal(integer);
    }

    public Int add(Int b)
    {
	return new Int(this.toBigInteger().add(b.toBigInteger()));
    }

    public Int sub(Int b)
    {
	return new Int(this.toBigInteger().subtract(b.toBigInteger()));
    }

    public Int mul(Int b)
    {
	return new Int(this.toBigInteger().multiply(b.toBigInteger()));
    }

    public Int divide(Int b)
    {
	return new Int(this.toBigInteger().divide(b.toBigInteger()));
    }

    public Numerical division(Int b)
    {
	return new Rational(this, b).make_normal();
    }

    public int compareTo(Int b)
    {
	return this.toBigInteger().compareTo(b.toBigInteger());
    }

    public boolean isPositive()
    {
	return this.toBigInteger().compareTo(BigInteger.ZERO) > 0;
    }

    public boolean isNegative()
    {
	return this.toBigInteger().compareTo(BigInteger.ZERO) < 0;
    }

    public String toString()
    {
	return integer.toString();
    }

    public static Int gcd(Int a, Int b)
    {
	return new Int(a.toBigInteger().gcd(b.toBigInteger()));
    }

    public static Int gcd(Int[] a)
    {
	if(a.length == 1)
	    return a[0];
	if(a.length == 2)
	    return gcd(a[0], a[1]);
	Int[] r = Set.rest(a);
	Int g = gcd(r);
	return Int.gcd(a[0], g);
    }

    public static Int lcm(Int a, Int b)
    {
	return a.mul(b).divide(gcd(a, b));
    }

    public Int mod(Int b)
    {
	return new Int(this.toBigInteger().mod(b.toBigInteger()));
    }

    public Int symmetric(Int m)
    {
	if(this.compareTo(ZERO) >= 0 && this.compareTo(m.divide(TWO)) <= 0)
	    return this;
	else
	    return this.sub(m);
    }

    public Int factorial()
    {
	Int f = Int.ONE;
	for(Int i = Int.ONE; i.compareTo(this) <= 0; i = i.add(Int.ONE))
	    f = f.mul(i);
	return f;
    }

    public Int[] base(Int b)
    {
	Vector<Int> list = new Vector<Int>();
	Int q = this;
	while(!q.equals(Int.ZERO))
	{
	    Int q_new = q.quot(b);
	    Int r_new = q.mod(b);
	    q = q_new;
	    list.add(r_new);
	}
	return list.toArray(new Int[list.size()]);
    }

    public boolean equals(Int b)
    {
	return this.compareTo(b) == 0;
    }

    public boolean isZero()
    {
	return this.equals(Int.ZERO);
    }

    public int toInt()
    {
	return integer.intValue();
    }

    public static Int[] extended_gcd(Int a, Int b)// returns [s, t, gcd(a,b)] ->
						  // s*a+t*b = gcd(a,b)
    {
	Int s = Int.ZERO;
	Int s_old = Int.ONE;
	Int t = Int.ONE;
	Int t_old = Int.ZERO;
	Int r = b;
	Int r_old = a;
	while(!r.equals(Int.ZERO))
	{
	    Int quotient = r_old.quot(r);
	    Int prov = r;
	    r = r_old.sub(quotient.mul(prov));
	    r_old = prov;
	    prov = s;
	    s = s_old.sub(quotient.mul(prov));
	    s_old = prov;
	    prov = t;
	    t = t_old.sub(quotient.mul(prov));
	    t_old = prov;
	}
	return new Int[] {s_old, t_old, r_old};
    }

    public static Int[] extended_gcd(Int[] a)// returns [s, t, gcd(a,b)] ->
					     // s*a+t*b = gcd(a,b)
    {
	if(a.length == 1)
	    return new Int[] {Int.ONE, a[0].abs()};
	if(a.length == 2)
	    return extended_gcd(a[0], a[1]);
	Int f = a[0];
	Int[] r = Set.rest(a);
	Int[] g = extended_gcd(r);
	Int[] d = extended_gcd(f, g[g.length - 1]);
	Int[] gcd = new Int[a.length + 1];
	gcd[0] = d[0];
	for(int i = 1; i < gcd.length - 1; i++)
	    gcd[i] = g[i - 1].mul(d[1]);
	gcd[gcd.length - 1] = d[2];
	return gcd;
    }

    public Int modInverse(Int modulus)
    {
	return new Int(this.toBigInteger().modInverse(modulus.toBigInteger()));
    }

    private Int quot(Int r)
    {
	return new Int(this.toBigInteger().divide(r.toBigInteger()));
    }

    public boolean isPrime()
    {
	return this.toBigInteger().isProbablePrime(15);
    }

    public static Int find_prime(Int a)
    {
	Int p = a;
	if(!p.isOdd())
	    p = p.add(Int.ONE);
	while(!p.isPrime())
	    p = p.add(Int.TWO);
	return p;
    }

    public static Int random_int(Int a, Int b)
    {

	Int c = b.sub(a);
	if(c.compareTo(new Int("1000000000")) <= 0)
	{
	    BigDecimal d = new BigDecimal(Math.random()).multiply(c.toBigDecimal());
	    return new Int(d.toBigInteger()).add(a);
	}
	else
	{
	    double d = Math.random();
	    if(d < 0.5)
		return random_int(a, a.add(c.divide(new Int("2"))));
	    else
		return random_int(a.add(c.divide(new Int("2"))), b);
	}
    }

    public boolean isOdd()
    {
	if(this.mod(Int.TWO).equals(Int.ZERO))
	    return false;
	else
	    return true;
    }

    public static Int integer_chinese_remainder_garner(Int[] U, Int[] M)
    {
	int n = M.length - 1;
	Int[] gamma = new Int[n + 1];
	for(int k = 1; k <= n; k++)
	{
	    Int product = M[0].mod(M[k]).symmetric(M[k]);
	    for(int i = 1; i <= k - 1 && k - 1 >= 1; i++)
	    {
		product = product.mul(M[i]).mod(M[k]).symmetric(M[k]);
	    }
	    gamma[k] = product.modInverse(M[k]).symmetric(M[k]);
	}
	Int[] v = new Int[n + 1];
	v[0] = U[0];
	for(int k = 1; k <= n; k++)
	{
	    Int tmp = v[k - 1];
	    for(int j = k - 2; j >= 0; j--)
		tmp = tmp.mul(M[j]).add(v[j]).mod(M[k]).symmetric(M[k]);
	    v[k] = U[k].sub(tmp).mul(gamma[k]).mod(M[k]).symmetric(M[k]);
	}
	Int u = v[n];
	for(int k = n - 1; k >= 0; k--)
	    u = u.mul(M[k]).add(v[k]);
	return u;
    }

    public static Int integer_chinese_remainder(Int[] M, Int[] X)
    {
	Int n = M[0];
	Int s = X[0];
	for(int i = 1; i < M.length; i++)
	{
	    Int x = X[i];
	    Int m = M[i];
	    Int[] e = Int.extended_gcd(n, m);
	    Int c = e[0];
	    Int d = e[1];
	    s = c.mul(n).mul(x).add(d.mul(m).mul(s));
	    n = n.mul(m);
	}
	return s.mod(n);
    }

    public Int[][] square_free_factor()
    {
	Vector<Int[]> ls = new Vector<>();
	Int[][] factors = this.factor();
	for(int i = 0; i < factors.length; i++)
	{
	    Int[] k = factors[i];
	    boolean added = false;
	    for(int j = 0; j < ls.size(); j++)
	    {
		if(ls.get(j)[1].equals(k[1]))
		{
		    ls.set(j, new Int[] {ls.get(j)[0].mul(k[0]), k[1]});
		    added = true;
		    break;
		}
	    }
	    if(!added)
	    {
		ls.add(k);
	    }
	}
	return ls.toArray(new Int[ls.size()][2]);
    }

    public Int[][] factor()
    {
	BigInteger[] list = factor(this.toBigInteger());
	Vector<Int[]> ls = new Vector<>();
	for(int i = 0; i < list.length; i++)
	{
	    Int k = new Int(list[i]);
	    boolean added = false;
	    for(int j = 0; j < ls.size(); j++)
	    {
		if(ls.get(j)[0].equals(k))
		{
		    ls.set(j, new Int[] {k, ls.get(j)[1].add(Int.ONE)});
		    added = true;
		    break;
		}
	    }
	    if(!added)
	    {
		ls.add(new Int[] {k, Int.ONE});
	    }
	}
	return ls.toArray(new Int[ls.size()][2]);
    }

    public Int[] factor_list()
    {
	BigInteger[] list = factor(this.toBigInteger());
	Int[] ls = new Int[list.length];
	for(int i = 0; i < list.length; i++)
	{
	    ls[i] = new Int(list[i]);
	}
	return ls;
    }

    // BigInteger factorization

    private final static SecureRandom random = new SecureRandom();

    public static BigInteger rho(BigInteger N)
    {
	BigInteger divisor;
	BigInteger c = new BigInteger(N.bitLength(), random);
	BigInteger x = new BigInteger(N.bitLength(), random);
	BigInteger xx = x;

	// check divisibility by 2
	if(N.mod(new BigInteger("2")).compareTo(new BigInteger("0")) == 0)
	    return new BigInteger("2");

	do {
	    x = x.multiply(x).mod(N).add(c).mod(N);
	    xx = xx.multiply(xx).mod(N).add(c).mod(N);
	    xx = xx.multiply(xx).mod(N).add(c).mod(N);
	    divisor = x.subtract(xx).gcd(N);
	}
	while((divisor.compareTo(new BigInteger("1"))) == 0);

	return divisor;
    }

    public static BigInteger[] factor(BigInteger N)
    {
	if(N.compareTo(new BigInteger("1")) == 0)
	    return new BigInteger[] {};
	if(N.isProbablePrime(20))
	    return new BigInteger[] {N};
	BigInteger divisor = rho(N);
	BigInteger[] f1 = factor(divisor);
	BigInteger[] f2 = factor(N.divide(divisor));
	BigInteger[] f3 = new BigInteger[f1.length + f2.length];
	for(int i = 0; i < f3.length; i++)
	{
	    if(i < f1.length)
		f3[i] = f1[i];
	    else
		f3[i] = f2[i - f1.length];
	}
	return f3;
    }

    public Int abs()
    {
	if(this.isNegative())
	    return this.mul(Int.NONE);
	return this;
    }

    public static Int min(Int a, Int b)
    {
	return a.compareTo(b) <= 0 ? a : b;
    }

    public static Int max(Int a, Int b)
    {
	return a.compareTo(b) >= 0 ? a : b;
    }

    public static Int max(Int... a)
    {
	if(a.length == 1)
	    return a[0];
	if(a.length == 2)
	    return Int.max(a[0], a[1]);
	Int[] s = Set.rest(a);
	return Int.max(Int.max(s), a[0]);
    }

    public static Int min(Int... a)
    {
	if(a.length == 1)
	    return a[0];
	if(a.length == 2)
	    return Int.min(a[0], a[1]);
	Int[] s = Set.rest(a);
	return Int.min(Int.min(s), a[0]);
    }

    public Int sign()
    {
	if(this.isPositive())
	    return Int.ONE;
	if(this.equals(Int.ZERO))
	    return Int.ZERO;
	return Int.NONE;
    }

    public Int[] all_divisors()
    {
	Int m = this.abs();
	for(Int i = Int.TWO; i.compareTo(m) <= 0; i = i.add(Int.ONE))
	{
	    if(m.mod(i).equals(Int.ZERO))
	    {
		Int n = m.quot(i);
		Int[] all = n.all_divisors();
		Int[] all_2 = new Int[all.length];
		for(int j = 0; j < all_2.length; j++)
		    all_2[j] = all[j].mul(i);
		return Set.union(all, all_2);
	    }
	}
	return new Int[] {Int.ONE, Int.NONE};
    }

    public Int square_root()
    {
	Int a_n = this;
	Int a_n_1 = Int.ZERO;
	while(a_n.sub(a_n_1).abs().compareTo(Int.ONE) > 0)
	{
	    a_n_1 = a_n;
	    a_n = a_n.add(this.divide(a_n)).divide(Int.TWO);
	}
	if(a_n.pow(Int.TWO).compareTo(this) < 0)
	    a_n = a_n.add(Int.ONE);
	return a_n;
    }

    public static Int[] getIntList(Int n, int length)
    {
	Int[] a = new Int[length];
	for(int i = 0; i < length; i++)
	    a[i] = n;
	return a;
    }

    public static Int binom(Int a, Int b)
    {
	Int n = Int.ONE;
	for(Int i = b.add(Int.ONE); i.compareTo(a) <= 0; i = i.add(Int.ONE))
	    n = n.mul(i);
	for(Int i = Int.TWO; i.compareTo(a.sub(b)) <= 0; i = i.add(Int.ONE))
	    n = n.divide(i);
	return n;
    }

    public static Int[] sieve(int n)
    {
	boolean[] l = new boolean[n + 1];
	for(int i = 0; i < l.length; i++)
	    l[i] = true;
	for(int i = 2; i < l.length; i++)
	{
	    if(l[i] == true)
	    {
		// Detect integer overflow
		int b = i > (Integer.MAX_VALUE) / i ? l.length : i * i;
		for(int j = b; j < l.length; j += i)
		    l[j] = false;
	    }
	}
	Vector<Int> v = new Vector<Int>();
	for(int i = 2; i < l.length; i++)
	    if(l[i] == true)
		v.add(new Int(i));
	return v.toArray(new Int[v.size()]);
    }

    public static Int[] sieve_odd(int n)
    {
	boolean[] l = new boolean[n / 2];
	for(int i = 0; i < l.length; i++)
	    l[i] = true;
	for(int i = 0; i < l.length; i++)
	{
	    if(l[i] == true)
	    {
		int number = 2 * i + 3;
		// Detect integer overflow
		int b = number > (Integer.MAX_VALUE) / number ? n + 2 : number * number;
		for(int j = b; j <= n + 1; j += 2 * number)
		{
		    if(j % 2 == 1)
			l[((j - 3) / 2)] = false;
		}
	    }
	}
	LinkedList<Int> v = new LinkedList<Int>();
	for(int i = 0; i < l.length; i++)
	    if(l[i] == true)
		v.add(new Int(2 * i + 3));
	return v.toArray(new Int[v.size()]);
    }

    public static Int[] prime_list(int n)
    {
	LinkedList<Int> l = new LinkedList<Int>();
	l.add(Int.TWO);
	Int k;
	for(int i = 3; i <= n; i += 2)
	{
	    k = new Int(i);
	    if(k.isPrime())
		l.add(k);
	}
	return l.toArray(new Int[l.size()]);
    }

    public static Int nth_prime(Int n)
    {
	if(n.equals(Int.ONE))
	    return Int.TWO;
	Int c = Int.TWO;
	Int i = Int.THREE;
	while(!c.equals(n))
	{
	    i = i.add(Int.TWO);
	    if(i.isPrime())
		c = c.add(Int.ONE);
	}
	return i;
    }

    public static boolean pairwise_relatively_prime(Int[] a)
    {
	if(a.length == 0)
	    return true;
	if(a.length == 1)
	    return true;
	Int[] r = Set.rest(a);
	if(pairwise_relatively_prime(r))
	{
	    for(int i = 0; i < r.length; i++)
		if(!gcd(a[0], r[i]).equals(Int.ONE))
		    return false;
	    return true;
	}
	else
	    return false;
    }

    @Override
    public int hashCode()
    {
	return integer.hashCode();
    }
}
