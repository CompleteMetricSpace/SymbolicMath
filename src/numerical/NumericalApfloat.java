package numerical;

import java.math.BigDecimal;

import org.apfloat.*;

import Symbolic.Decimal;
import Symbolic.Rational;

public class NumericalApfloat 
{

	public static Apcomplex to_complex(Decimal[] x, int p)
	{
		return new Apcomplex(new Apfloat(x[0].toBigDecimal(), p), new Apfloat(x[1].toBigDecimal(), p));
	}
	
	public static Decimal[] to_decimal(Apcomplex x, int p)
	{
		
		return new Decimal[]{new Decimal(new BigDecimal(x.real().toString())), new Decimal(new BigDecimal(x.imag().toString()))};
	}
	
	public static Decimal[] exp(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.exp(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] log(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.log(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] pow(Decimal[] x, Decimal[] y, int p)
	{
		Apcomplex X = to_complex(x, p);
		Apcomplex Y = to_complex(y, p);
		X = ApcomplexMath.pow(X, Y);
		return to_decimal(X, p);
	}
	
	public static Decimal[] sin(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.sin(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] cos(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.cos(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] tan(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.tan(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] arcsin(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.asin(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] arccos(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.acos(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] arctan(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.atan(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] sinh(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.sinh(X);
		return to_decimal(X, p);
	}
	
	public static Decimal[] cosh(Decimal[] x, int p)
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.cosh(X);
		return to_decimal(X, p);
	}

	public static Decimal[] abs(Decimal[] x, int p) 
	{
		Apcomplex X = to_complex(x, p);
		X = ApcomplexMath.abs(X);
		return to_decimal(X, p);
	}
	
}
