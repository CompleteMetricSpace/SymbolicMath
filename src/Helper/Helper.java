package Helper;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Predicate;



import Expression.Expr;
import Expression.Operator;
import Simplification.*;

public class Helper
{
    public static Pair<List<Expr>, List<Expr>> sort(Expr[] list, Predicate<Expr> p)
    {
	return sort(Arrays.asList(list), p);
    }
    
    public static Pair<List<Expr>, List<Expr>> sort(List<Expr> list, Predicate<Expr> p)
    {
	List<Expr> trueList = new LinkedList<>();
	List<Expr> falseList = new LinkedList<>();
	list.forEach(expr -> {
	    if(p.test(expr))
		trueList.add(expr);
	    else
		falseList.add(expr);
	});
	return new Pair<>(trueList, falseList);
    }
    
    public static Expr apply(List<Expr> list, Operator operator)
    {
	return Simplification.simplify_recursive(new Expr(operator, list.toArray(new Expr[list.size()])));
    }
}
