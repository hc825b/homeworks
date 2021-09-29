method pm(x: int, y: int) returns (res: int)
    requires x >= 0 && y >= 0
    ensures res == x * y
{
    var a: int := x;
    var b: int := y;
    res := 0;
    while (a > 0)
        invariant a>=0 && a*b + res == x*y
        decreases a
    {
        if ((a % 2) == 1) {
            res := res + b;
        }
        a := a / 2;
        assert a >= 0;
        b := b * 2;
    }
    return res;
}