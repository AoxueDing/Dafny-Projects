include "permutation.dfy"
include "sorted.dfy"
include "arraySplit.dfy"
include "merge.dfy"

method MergeSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures Permutations(a[..], old(a[..]))
{
  if (a.Length <= 1) {
    return;  // Base case: Array is already sorted if it has 1 or 0 elements
  }

  var mid := a.Length / 2;
  var left, right := ArraySplit(a);

  MergeSort(left);
  MergeSort(right);

  var merged := Merge(left, right);

  var i := 0;
  while (i < a.Length)
  {
    a[i] := merged[i];
    i := i + 1;
  }
}
