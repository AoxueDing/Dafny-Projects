include "permutation.dfy" // Definition of permutation properties
include "sorted.dfy"      // Definition of sorted-ness for sequences

method SelectionSort (a : array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures Permutations (a[..], old(a[..]))
{
  var n := a.Length;
  var i := 0;

  while (i < n)
    invariant 0 <= i <= n
    invariant Sorted(a[..i])
    invariant Permutations(a[..], old(a[..]))
  {
    var minIdx := i;
    var j := i + 1;

    while (j < n)
      invariant i < j <= n
      invariant IsMinIndex(minIdx, a[i..j])
    {
      if (a[j] < a[minIdx]) {
        minIdx := j;
      }
      j := j + 1;
    }
    // Swap a[i] and a[minIdx]
    if (i != minIdx) {
      var temp := a[i];
      a[i] := a[minIdx];
      a[minIdx] := temp;
    }

    i := i + 1;
  }
}