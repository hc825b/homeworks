
///<summary>
///  Iteration implementation for immutable set
///</summary>
iterator Iter<T>(s: set<T>) yields (x: T)
  yield ensures x in s && x !in xs[..|xs|-1];
  ensures s == set z | z in xs;
{
  var r := s;
  while (r != {})
    invariant forall z :: z in xs ==> x !in r; // r and xs are disjoint
    invariant s == r + set z | z in xs;
  {
    var y :| y in r;
    r, x := r - {y}, y;
    yield;
    assert y == xs[|xs|-1]; // needed as a lemma to prove loop invariant
  }
}

method Main()
{
  var i := 1;

  var list : seq<int> := [1, 2];

  while(i < 10)
    decreases 11 - i
  {
  i := i + 1;
  var S : set<int> := set z | z < i && z >= 1;

  var value := list[0];
  list := list[1..];

  var it := new Iter(S);
  ghost var X := {};
  while(true)
    invariant it.Valid() && fresh(it._new);
    invariant X == set z | z in it.xs;
    decreases it.s - X;
  {
    // Iterator Code
    var more := it.MoveNext();
    if(!more){ break;}
    X := X + {it.x};

    // Custom Code
    list := list + [it.x];
  }
  }
}
