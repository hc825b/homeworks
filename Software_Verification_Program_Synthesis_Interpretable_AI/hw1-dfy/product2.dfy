method Product2 (m: nat, n: nat) returns (res:nat) 
    ensures res == m * n; 
{   
    var m1: nat := m; 
    var n1: nat; 
    res := 0; 
    while (m1 > 0)
        invariant m1 >= 0 && res == (m - m1) * n
    { 
        n1 := n; 
        while (n1 > 0)  
            invariant n1 >= 0 && res == (m - m1) * n + (n - n1)
        { 
            res := res + 1;
            n1 := n1 - 1; 
        } 
        m1 := m1 - 1; 
    } 
 }

