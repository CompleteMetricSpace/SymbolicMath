package Symbolic;


public class Rational extends Numerical
{

	final public static Rational HALF = new Rational(Int.ONE, Int.TWO);
	final public static Rational FOURTH = new Rational(Int.ONE, Int.FOUR);
	
	Int n, d;
	
	public Rational(Int a, Int b)
	{
		n = a;	d = b;
	}
	
	public Rational(Int a)
	{
		n = a;	d = Int.ONE;
	}
	
	public Rational(String a, String b)
	{
		n = new Int(a);	d = new Int(b);
	}
	
	public Rational(String a)
	{
		int index = a.indexOf(".");
		if(index == -1)
		{
			n = new Int(a);
			d = Int.ONE;
		}
		else
		{
			int c = a.length()-index;
			String l = a.substring(0, index)+a.substring(index+1, a.length());
			n = new Int(l);
			d = (Int)Int.TEN.pow(new Int(c));
		}
	}
	
	public Int getNumerator()
	{
		return n;
	}
	
	public Int getDenominator()
	{
		return d;
	}
	
	public Rational normal()
	{
		Int gcd = Int.gcd(n, d);
		Int a = n.divide(gcd), b = d.divide(gcd);
		if(a.isNegative() && b.isNegative())
			return new Rational(a.mul(Int.NONE), b.mul(Int.NONE));
		if(a.isNegative() && b.isPositive())
			return new Rational(a, b);
		if(a.isPositive() && b.isNegative())
			return new Rational(a.mul(Int.NONE), b.mul(Int.NONE));
		return new Rational(a, b);
	}
	
	private Rational normal_sign()
	{
		if(n.isNegative() && d.isNegative())
			return new Rational(n.mul(Int.NONE), d.mul(Int.NONE));
		if(n.isNegative() && d.isPositive())
			return new Rational(n, d);
		if(n.isPositive() && d.isNegative())
			return new Rational(n.mul(Int.NONE), d.mul(Int.NONE));
		return new Rational(n, d);
	}
	
	public Rational inverse()
	{
		return new Rational(d, n).normal();
	}
	
	public Rational add(Rational b)
	{
		Int k = Int.gcd(this.getDenominator(), b.getDenominator());
		if(k.equals(Int.ONE))
			return new Rational(this.getNumerator().mul(b.getDenominator()).add(this.getDenominator().mul(b.getNumerator())),
						this.getDenominator().mul(b.getDenominator()));
		Int t = this.getNumerator().mul(b.getDenominator().divide(k)).add(b.getNumerator().mul(this.getDenominator().divide(k)));
		Int l = Int.gcd(t, k);
		return new Rational(t.divide(l), this.getDenominator().divide(k).mul(b.getDenominator().divide(l))).normal_sign();
	}
	
	public Rational sub(Rational b)
	{
		Int k = Int.gcd(this.getDenominator(), b.getDenominator());
		if(k.equals(Int.ONE))
			return new Rational(this.getNumerator().mul(b.getDenominator()).sub(this.getDenominator().mul(b.getNumerator())),
						this.getDenominator().mul(b.getDenominator()));
		Int t = this.getNumerator().mul(b.getDenominator().divide(k)).sub(b.getNumerator().mul(this.getDenominator().divide(k)));
		Int l = Int.gcd(t, k);
		return new Rational(t.divide(l), this.getDenominator().divide(k).mul(b.getDenominator().divide(l))).normal_sign();
	}
	
	public Rational mul(Rational b)
	{
		return new Rational(n.mul(b.getNumerator()), d.mul(b.getDenominator())).normal();
	}
	
	public Rational div(Rational b)
	{
		return this.mul(b.inverse());
	}
	
	public Rational add(Int b)
	{
		return this.add(new Rational(b, Int.ONE));
	}
	
	public Rational mul(Int b)
	{
		return this.mul(new Rational(b, Int.ONE));
	}
	
	public Rational sub(Int b)
	{
		return this.sub(new Rational(b, Int.ONE));
	}
	
	public Rational div(Int b)
	{
		return this.div(new Rational(b, Int.ONE));
	}
	
	public boolean equals(Rational b)
	{
		return n.mul(b.getDenominator()).equals(d.mul(b.getNumerator()));
	}
	
	public int compareTo(Rational b)
	{
		Rational a = this.normal();
		b = b.normal();
		return a.getNumerator().mul(b.getDenominator()).compareTo(b.getNumerator().mul(a.getDenominator()));
	}
	
	public String toString()
	{
		return n+"/"+d;
	}
	
	public static Rational reconstruct(Int n, Int m, Int N, Int D)
	{
		Int v_1 = m;
		Int v_2 = Int.ZERO;
		Int w_1 = n;
		Int w_2 = Int.ONE;
		while(w_1.compareTo(N) > 0)
		{
			Int q = v_1.divide(w_1);
			Int z_1 = v_1.sub(q.mul(w_1));
			Int z_2 = v_2.sub(q.mul(w_2));
			v_1 = w_1; v_2 = w_2;
			w_1 = z_1; w_2 = z_2;
		}
		if(w_2.isNegative())
		{
			w_1 = w_1.mul(Int.NONE);
			w_2 = w_2.mul(Int.NONE);
		}
		if(w_1.compareTo(D) < 0 && Int.gcd(w_1, w_2).equals(Int.ONE))
			return new Rational(w_1, w_2);
		return null;
	}
}
