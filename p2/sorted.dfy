include "permutation.dfy"

// Definition of sortedness for a sequence.

predicate Sorted (a : seq<int>)
{
    forall i, j : int :: 0 <= i <= j < |a| ==> a[i] <= a[j]
}

// Any suffix of a sorted sequence is also sorted.

lemma SortedSuffix (a : seq<int>, i : int)
    requires Sorted (a)
    requires 0 <= i < |a|
    ensures Sorted (a[i..])
{ }

// Any prefix of a sorted sequence is also sorted.

lemma SortedPrefix (a : seq<int>, i : int)
    requires Sorted (a)
    requires 0 <= i < |a|
    ensures Sorted (a[..i])
{ }

// If two adjacent sub-slices of a sequence prefix are sorted,
// and the last element (if it exists) of the first subslice
// is <= the first element (if it exists) of the second subslide, then
// the prefix is also sorted.

lemma SortedConcatenation (i : int, j : int, a : seq<int>)
    requires 0 <= i <= j < |a|
    requires Sorted(a[..i]) && Sorted(a[i..j])
    requires i > 0 ==> (a[i-1] < a[i])
    ensures Sorted(a[..j])
{ }

// Definition of when every element in a is <= every element in b.
// "SeqLeqSeq" is short for "Sequence Less-than-or-equal-to Sequence"

predicate SeqLeqSeq (a : seq<int>, b : seq<int>)
{
    forall i, j : int :: (0 <= i < |a| && 0 <= j < |b|) ==> a[i] <= b[j]
}

// Alternative characterization of SeqLeqSeq.

predicate SLSAlt (a : seq<int>, b : seq<int>)
{
    forall m, n : int :: (m in a && n in b) ==> m <= n
}

// SeqLeqSeq implies alternative characterization.

lemma SLSImpliesSLSAlt (a : seq<int>, b : seq<int>)
    requires SeqLeqSeq (a, b)
    ensures SLSAlt(a, b)
{ }

// Alternative characterization implies SeqLeqSeq.

lemma SLSAltImpliesSLS (a : seq<int>, b : seq<int>)
    requires SLSAlt (a, b)
    ensures SeqLeqSeq (a, b)
{ 
    assert forall i, j : int :: ((0 <= i < |a|) && (0 <= j < |b|)) ==> ((a[i] in a) && (b[j] in b));
}

// If b is sorted and every element in a is <= every element in b,
// then every element in the concatenation of a and b[..i] is <= every element
// in b[i..].

lemma SLSSortedShift (a : seq<int>, b : seq<int>, i : int)
    requires SeqLeqSeq (a, b)
    requires Sorted (b)
    requires 0 <= i < |b|
    ensures SeqLeqSeq (a + b[..i], b[i..])
{ }

// Definition of when every element to left of i is <= to every element at or 
// to the right of i.

predicate LeftLeqRight (a : seq<int>, i : int)
    requires 0 <= i <= |a|
{
    forall j, k : int :: 0 <= j < i && i <= k < |a| ==> a[j] <= a[k]
}

// LeftLeqRight implies SeqLeqSeq

lemma LLRImpliesSLS (a : seq<int>, i : int)
    requires 0 <= i <= |a|
    requires LeftLeqRight (a, i)
    ensures SeqLeqSeq (a[..i], a[i..])
{ }

// SeqLeqSeq implies LeftLeqRight.

lemma SLSImpliesLLR (a : seq<int>, b : seq<int>)
    requires SeqLeqSeq (a, b)
    ensures LeftLeqRight (a+b, |a|)
{ }

// Permutations preserve SeqLeqSeq on the left.

lemma PermLeftPreservesSLS (a1 : seq<int>, a2 : seq<int>, b : seq<int>)
    requires SeqLeqSeq (a1, b)
    requires Permutations (a1, a2)
    ensures SeqLeqSeq (a2, b)
{
    PermSameElements (a1, a2);
    assert forall m : int :: m in a2 ==> m in a1;
    assert SLSAlt (a2, b);
    SLSAltImpliesSLS(a2, b);
}

// Permutations preserve SeqLeqSeq on the right.

lemma PermRightPreservesSLS (a : seq<int>, b1 : seq<int>, b2 : seq<int>)
    requires SeqLeqSeq (a, b1)
    requires Permutations (b1, b2)
    ensures SeqLeqSeq (a, b2)
{
    PermSameElements (b1, b2);
    assert forall m : int :: m in b1 ==> m in b2;
    assert SLSAlt (a, b2);
    SLSAltImpliesSLS(a, b2);
}

// Permutations preserve SeqLeqSeq.

lemma PermPreservesSLS (a1 : seq<int>, a2 : seq<int>, b1 : seq<int>, b2 : seq<int>)
    requires SeqLeqSeq (a1, b1)
    requires Permutations (a1, a2)
    requires Permutations (b1, b2)
    ensures SeqLeqSeq (a2, b2)
{
    PermLeftPreservesSLS (a1, a2, b1);
    PermRightPreservesSLS (a2, b1, b2);
}

// Definition of index being the minimum element in a sequence.

predicate IsMinIndex (i : int, a : seq<int>)
{
    0 <= i < |a| &&
    forall j : int :: 0 <= j < |a| ==> a[i] <= a[j]
}