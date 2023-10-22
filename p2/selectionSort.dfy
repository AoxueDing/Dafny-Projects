include "permutation.dfy" // Definition of permutation properties
include "sorted.dfy"      // Definition of sorted-ness for sequences

method SelectionSort (a : array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures Permutations (a[..], old(a[..]))
{
  var n := 0;
  while (n != a.Length)
    invariant 0 <= n <= a.Length
    //invariant Sorted(a[..n])
    invariant forall i,j :: 0 <= i < n <= j < a.Length ==> a[i] <= a[j]
    invariant forall k1, k2 :: 0 <= k1 < k2 < n ==> a[k1] <= a[k2]
    invariant Permutations (a[..], old(a[..]))
  {
    var mindex := n;
    var m := n + 1;
    while (m != a.Length)
      invariant n <= m <= a.Length
      invariant n <= mindex < m <= a.Length
      invariant forall i :: n <= i < m ==> a[mindex] <= a[i]
    {
      if (a[m] < a[mindex]) {
        mindex := m;
      }
      m := m + 1;
    }
    a[n], a[mindex] := a[mindex], a[n] ;
    n := n + 1;
  }

}