///<summary>
///  Iteration implementation for immutable set
///</summary>
iterator Iter<T>(S: set<T>) yields (x: T)
  yield ensures x in S && x !in xs[..|xs|-1];
  ensures S == set z | z in xs;
{
  var R := S;
  while (R != {})
    invariant forall z :: z in xs ==> z !in R; // R and set(xs) are disjoint
    invariant S == R + set z | z in xs;
  {
    var y :| y in R;
    R, x := R - {y}, y;
    yield;
    assert y == xs[|xs|-1]; // needed as a lemma to prove loop invariant
  }
}

/// <summary>
/// 
/// </summary>
class WorkListTrait<T>
{
  var tmp : T;

  constructor () {}

  method Enqueue(value: T)
    modifies this
  {}

  method Dequeue() returns (value: T)
    modifies this
  {
    return tmp;
  }

  predicate method empty()
  {
    // TODO
    false
  }
}

datatype EdgeBase<T(==)> = EdgeBase(src: T, tgt: T)
datatype DiGraphBase<T(==)> = DiGraphBase(V: set<T>, E: set<EdgeBase<T>>)
///<summary>
///  Class invariant of a directed graph
///  The two ends of all edges must be in the graph
///</summary>
predicate Valid<T(==)>(G: DiGraphBase<T>)
{
  forall e :: e in G.E
     ==> e.src in G.V && e.tgt in G.V
}

datatype NodeT = NIL | NodeT(nat)
datatype DistT = INF | DistT(l: int)
datatype Color = WHITE | GREY | BLACK
datatype NodeLabel = NodeLabel(color: Color, d: DistT, pred: NodeT)

/// <summary>
/// </summary>
class SearchAlgorithmBase
{
  var labels : map<NodeT, NodeLabel>;

  ///<summary>
  ///</summary>
  method Main(G: DiGraphBase<NodeT>, s: NodeT)
    modifies this;
    requires Valid(G) && s in G.V;
  {
    Init(G);
    Search(G, s);
  }

  ///<summary>
  ///  Initialize color of all nodes in G to WHITE
  ///  <param name="G">given directed graph</param>
  ///</summary>
  method Init(G: DiGraphBase<NodeT>)
    modifies this;
    ensures forall v :: v in G.V ==>
            v in labels && labels[v].color == WHITE;
  {
    var it := new Iter(G.V);
    ghost var X := {};
    while (true)
      // Iterator Invariants
      invariant it.Valid() && fresh(it._new);
      invariant X == set z | z in it.xs;
      decreases it.S - X;
      // Custom
      invariant forall v :: v in X
                ==> v in labels && labels[v].color == WHITE;
    {
      // Iterator code
      var more := it.MoveNext();
      if(!more){ break;}
      X := X + {it.x};

      // Custom code
      var u := it.x;
      labels := labels[u := NodeLabel(WHITE, INF, NIL)];
    }
  }
/* Another version follows for-loop structure
  {
    var it := new Iter(G.V);
    var more := it.MoveNext();
    ghost var t := {};
    while (more)
      invariant (more ==> it.Valid()) && fresh(it._new);
      invariant more ==>
        (it.x in G.V && it.x !in t && (t + {it.x} == set z | z in it.xs));
      invariant t <= G.V && (more || t == G.V);
      invariant forall v :: v in t ==>
                  v in color && color[v] == WHITE;
      decreases G.V - t;
    {
      color := color[it.x := WHITE];
      t := t + {it.x};
      more := it.MoveNext();
    }
  }
*/

  method Search(G: DiGraphBase<NodeT>, s : NodeT)
    modifies this;
    requires Valid(G) && s in G.V;
    requires forall v :: v in G.V ==>
             v in labels && labels[v].color == WHITE;
  {
    var s_label := labels[s];
    s_label := s_label.(color := GREY, d := DistT(0));
    labels := labels[s := s_label];
/*
    var worklist := new WorkListTrait<NodeT>();
    worklist.Enqueue(s);
    ghost var black : set<NodeT> := {};
    while ( !worklist.empty() )
      invariant true;
      decreases G.V - black;
*/
    if(true)
    {
//      var u := worklist.Dequeue();
      var u := s;

      // Iterate through all outgoing edges of node u
      var edge_u := set e | e in G.E && e.src == u;
      var it := new Iter(edge_u);
      ghost var X := {};
      while(true)
        // Iterator Invariants
        invariant it.Valid() && fresh(it._new);
        invariant X == set z | z in it.xs;
        decreases it.S - X;
        // Custom Invariants
        invariant forall v :: v in G.V ==> v in labels;
        invariant labels[u].d != INF;
      {
        // Iterator Code
        var more := it.MoveNext();
        if(!more){ break;}
        X := X + {it.x};

        // Custom Code
        var v := it.x.tgt;
        if(labels[v].color == WHITE)
        {
          var v_label := labels[v];
          assert labels[u].d != INF;
          v_label := v_label.(
            color := GREY,
            d := DistT(labels[u].d.l + 1),
            pred := u
          );
          labels := labels[v := v_label];
          //worklist.Enqueue(v);
        }
      }
      // Color node u to black
      labels := labels[u := labels[u].(color := BLACK)];
//      black := black + {u};
    }
  }
}
