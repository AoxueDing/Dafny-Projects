include "permutation.dfy"
include "sorted.dfy"
include "arraySplit.dfy"
include "merge.dfy"

method MergeSort(a: array<int>)
  modifies a
  ensures Sorted(a[..])
  ensures Permutations(a[..], old(a[..]))
  decreases a.Length
{
  if (a.Length <= 1) {
    return;  // Base case: Array is already sorted if it has 1 or 0 elements
  }

  var left, right := ArraySplit(a);
  MergeSort(left);
  MergeSort(right);

  var merged := Merge(left, right);

  var i := 0;
  while (i < a.Length)
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == merged[k]
    invariant forall i, j : int :: 0 <= i <= j < merged.Length ==> merged[i] <= merged[j]
    invariant Permutations(merged[..i], a[..i])
  {
    a[i] := merged[i];
    i := i + 1;
  }
  assert multiset(a[..]) == multiset(old(a[..]));

}
