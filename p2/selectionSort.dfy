include "permutation.dfy" // Definition of permutation properties
include "sorted.dfy"      // Definition of sorted-ness for sequences

method SelectionSort (a : array<int>)
    modifies a
    ensures Sorted(a[..])
    ensures Permutations (a[..], old(a[..]))
{
    // TO DO
}