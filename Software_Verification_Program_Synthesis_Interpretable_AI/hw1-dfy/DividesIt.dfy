method DividesIt(x: int, y: int, d: int) returns (r: int)
  requires x >= 0 &&  y >=0  && d>0 && x%d==0 && y%d==0
  ensures r % d==0
{
  var x1: int := x;
  var y1: int := y;
  while (x1 > 0 && y1 > 0) 
    // write invariant here
    invariant x1>=0 && y1>=0 && x1%d==0 && y1%d==0
    decreases x1+y1
  {
    if (x1 >= y1) 
     {  DivLemma( d,x1,y1 ); 
        x1 := x1 - y1; }
    else 
     { 
       DivLemma( d,x1,y1 );
       y1 := y1 - x1;
     }
  }
  r:=x1;

  if (x1==0) 
    {r:=y1; }
  else
    {r:=x1;}
}

lemma DivLemma(d: int, a: int, b: int)
requires d>0 && a>0 && b>0 && a%d==0 && b%d==0 
ensures (a-b)%d==0  && (b-a) % d==0 
{
  assume (a-b)%d==0 && (b-a)%d==0;
}

