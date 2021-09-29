method Product1 (m: nat, n: nat) returns (res:nat) 
    ensures res == m * n; 
{   
    var m1: nat := 0; 
    var n1: nat := 0; 
    res := 0; 
    while (m1 < m)
       invariant m1 <= m && res == m1 * n
    { 
        n1 := 0; 
        while (n1 < n)
            invariant n1 <= n && res == m1 * n + n1
        { 
            res := res + 1;
            n1 := n1 + 1; 
        } 
        m1 := m1 + 1; 
    }
 }
