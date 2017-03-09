///<summary>
///  Iterator implementation for immutable set
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

datatype EdgeBase<T(==)> = EdgeBase(src: T, tgt: T)
datatype DiGraphBase<T(==)> = DiGraphBase(V: set<T>, E: set<EdgeBase<T>>)
///<summary>
///  Class invariant of a directed graph
///  The two ends of all edges must be in the graph
///</summary>
predicate Valid<T(==)>(G: DiGraphBase<T>)
{
  (forall e :: e in G.E
     ==> e.src in G.V && e.tgt in G.V) && (|G.V|>=1)
}
///<summary>
///  Check if every node in the sequence is distinct
///</summary>
predicate Unique<T(==)>(list : seq<T>)
{
  forall i :: 0 <= i < |list| ==>
    forall j :: 0 <= j < |list| ==> list[i] == list[j] ==> i == j
}
///<summary>
///  Check if 'path' is a simple path on 'G'
///</summary>
predicate ValidSimplePath<T(==)>(G: DiGraphBase<T>, path: seq<T>)
  requires Valid(G)
  decreases |path|
{
  |path| >= 1 && Unique(path)
  && forall v :: v in path ==> v in G.V
  && (|path| > 1 ==>
     exists e :: e in G.E && e.src == path[|path|-2] && e.tgt == path[|path|-1]
              && ValidSimplePath(G, path[..(|path|-1)]))
}
///<summary>
///  Check if 's' can reach 't' via path 'p' on 'G'
///</summary>
predicate Reachable<T(==)>(G: DiGraphBase<T>, s: T, t:T, p: seq<T>)
  requires Valid(G)
{
  |p| > 0 && p[0] == s && p[|p|-1] == t
  && ValidSimplePath(G, p) 
}

datatype NodeT = NIL | NodeT(nat)
datatype DistT = INF | DistT(l: int)
datatype Color = WHITE | GREY | BLACK
datatype NodeLabel = NodeLabel(color: Color, d: DistT, ghost path:seq<NodeT>)

/// <summary>
/// </summary>
class SearchAlgorithmBase
{
  var labels : map<NodeT, NodeLabel>;

  predicate ValidLabels(G : DiGraphBase<NodeT>)
    reads `labels
  {
    forall v :: v in G.V ==> v in labels
  }
  predicate InitializedLabels(G : DiGraphBase<NodeT>)
    reads `labels
    requires ValidLabels(G)
  {
    forall v :: v in G.V
       ==> (labels[v].color == WHITE
         && labels[v].d == INF
         && labels[v].path == [])
  }

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
    ensures ValidLabels(G) && InitializedLabels(G); 
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
            ==> (v in labels && labels[v].color == WHITE
                 && labels[v].d == INF && labels[v].path == []);
    {
      // Iterator code
      var more := it.MoveNext();
      if(!more){ break;}
      X := X + {it.x};

      // Custom code
      var u := it.x;
      labels := labels[u := NodeLabel(WHITE, INF, [])];
    }
    assert X == G.V;
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

  ///<summary>
  ///  Implement search algorithm by coloring nodes
  ///  <param name="G">given directed graph</param>
  ///  <param name="s">given starting node</param>
  ///</summary>
  method Search(G: DiGraphBase<NodeT>, s : NodeT)
    modifies this;
    requires Valid(G) && s in G.V;
    requires ValidLabels(G) && InitializedLabels(G); 
    ensures  ValidLabels(G) 
    ensures  forall v :: v in G.V && labels[v].color == BLACK
         ==> labels[v].d != INF && Reachable(G, s, v, labels[v].path);
  {
    var s_label := labels[s];
    s_label := s_label.(color := GREY, d := DistT(0), path := [s]);
    labels := labels[s := s_label];

    var worklist : seq<NodeT> := [s];

    ghost var B := {};
    while |worklist| > 0
      // Aux_LIs_0
      invariant ValidLabels(G);
      invariant B == set v | v in G.V && labels[v].color == BLACK;
      // LI_1
      invariant forall v :: v in worklist ==> v in G.V;
      // LI_2 depends on Aux_LIs_0, LI_1
      invariant forall v :: v in worklist ==> labels[v].color != WHITE;
      // LI_3 depends on LI_2
      invariant Unique<NodeT>(worklist);
      // LI_4 depends on LI_3
      invariant forall v :: v in worklist ==> labels[v].color != BLACK;
      // LI_5 depends on Aux LIs, LI_1
      invariant forall v :: v in worklist ==> labels[v].d != INF;
      // Termination depends on LI_3, LI_4, Aux_LIs_0
      decreases G.V - B;
      // LI_7
      invariant forall v,n :: v in G.V && n in G.V && labels[v].color == WHITE
                          ==> v !in labels[n].path
      // LI_8 depends on LI_7
      invariant forall v :: v in worklist
                        ==> Reachable(G, s, v, labels[v].path);
      // LI_9
      invariant forall v :: v in B
            ==> labels[v].d != INF && Reachable(G, s, v, labels[v].path);
    {
      // Dequeue
      var u := worklist[0];
      worklist := worklist[1..];

      // Color node u to black
      labels := labels[u := labels[u].(color := BLACK)];
      B := B + {u};

      // Iterate through all outgoing edges of node u
      var edge_u := set e | e in G.E && e.src == u;
      var it := new Iter(edge_u);
      ghost var X := {};
      ghost var old_labels := labels;
      while(true)
        // Iterator Invariants
        invariant it.Valid() && fresh(it._new);
        invariant X == set z | z in it.xs;
        decreases it.S - X;
        // Custom Invariants
        // Aux_LIs_0
        invariant ValidLabels(G) && forall v :: v in G.V ==> v in old_labels;
        invariant B == set v | v in G.V && labels[v].color == BLACK;
        // LI_1
        invariant forall v :: v in worklist ==> v in G.V;
        // LI_2 depends on Aux_LIs_0, LI_1
        invariant forall v :: v in worklist ==> labels[v].color != WHITE;
        // LI_3 depends on LI_2
        invariant Unique<NodeT>(worklist);
        // LI_4 depends on LI_3
        invariant forall v :: v in worklist ==> labels[v].color != BLACK;
        // LI_5 depends on Aux_LIs_0, LI_1
        invariant forall v :: v in worklist ==> labels[v].d != INF;
        // LI_6 depends on LI_5
        invariant u in labels && labels[u].d != INF;
        // LI_7
        invariant forall v,n :: v in G.V && n in G.V && labels[v].color == WHITE
              ==> v !in labels[n].path
        // LI_8 depends on LI_7
        invariant Reachable(G, s, u, labels[u].path)
               && forall v :: v in worklist
                          ==> Reachable(G, s, v, labels[v].path)
        // LI_9
        invariant forall v :: v in B 
              ==> labels[v].d != INF && Reachable(G, s, v, labels[v].path);
      {
        // Iterator Code
        var more := it.MoveNext();
        if(!more){ break;}
        X := X + {it.x};

        // Custom Code
        var v : NodeT := it.x.tgt;
        if(labels[v].color == WHITE)
        {
          var v_label := labels[v];
          assert labels[u].d != INF; // Proven by LI_6
          v_label := v_label.(
            color := GREY,
            d := DistT(labels[u].d.l + 1),
            path := labels[u].path + [v]
          );
          assert Reachable(G, s, v, v_label.path); // Proven by LI_7. Help prove LI_8
          labels := labels[v := v_label];
          // Enqueue
          worklist := worklist + [v];
        }
      }
    }
  }
}
