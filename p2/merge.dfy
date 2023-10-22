include "permutation.dfy"
include "sorted.dfy"

method Merge(a: array<int>, b: array<int>) returns(c: array<int>)
  requires Sorted(a[..])
  requires Sorted(b[..])
  ensures fresh(c)  // c is newly created
  ensures Sorted(c[..])
  ensures Permutations(old(a[..]) + old(b[..]), c[..])
{
  var i := 0;
  var j := 0;
  var k := 0;
  c := new int[a.Length + b.Length];

  while (k < c.Length)
    invariant 0 <= i <= a.Length
    invariant 0 <= j <= b.Length
    invariant 0 <= k <= c.Length
    invariant k == i + j
    invariant SeqLeqSeq(c[..k], a[i..])
    invariant SeqLeqSeq(c[..k], b[j..])
    invariant Sorted(c[..k])
    invariant Permutations(a[..i] + b[..j], c[..k])
  {
    if (i < a.Length && (j == b.Length || a[i] <= b[j])) {
      c[k] := a[i];
      i := i + 1;
    } else {
      c[k] := b[j];
      j := j + 1;
    }
    k := k + 1;
  }

  assert a[..i] == old(a[..]);
  assert b[..j] == old(b[..]);
  assert c[..k] == c[..];
  assert Sorted(c[..]);
}

