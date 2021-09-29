
method Half(x: int) returns (r: int)
  requires x >= 0
  ensures r == x/2
{
  var i: int :=0;
  var x1: int:=x/2 * 2;
  assert x1 == (x1/2)*2 ; //  x1 is even
  assert x1 %2 ==0;       //  x1 is even (written differently)
  assert x1/2 == x/2;     //  half of x1 should be half of x

  r:=0;

  while (i<x1) 
    // write invariant here
    invariant i <=x1
    invariant r == i/2 && i%2 == 0
    decreases x1-i
  {
     r:=r+1; i:=i+2;
  }

}


