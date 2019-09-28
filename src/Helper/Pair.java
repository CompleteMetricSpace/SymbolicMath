package Helper;

public class Pair<U, V>
{
    U u;
    V v;

    public Pair(U u, V v)
    {
        this.u = u;
        this.v = v;
    }

    public U getFirst()
    {
        return u;
    }

    public V getSecond()
    {
        return v;
    }

    public void setFirst(U u)
    {
        this.u = u;
    }

    public void setSecond(V v)
    {
        this.v = v;
    }

    public String toString()
    {
        return "Pair[" + u + " | " + v + "]";
    }

    
}
