// Definition of when sequence a is a permutation of sequence b.

predicate Permutations (a : seq<int>, b : seq<int>)
{
    multiset(a) == multiset(b)
}

// Two sequences that are permutations of each other contain the same elements.

lemma PermSameElements (a : seq<int>, b : seq<int>)
    requires Permutations(a, b)
    ensures forall m : int :: m in a <==> m in b
{ 
    assert forall m : int :: m in a <==> m in multiset(a);
}

// Two sequences that are permutations of each other have the same length.

lemma PermLength (a : seq<int>, b : seq<int>)
    requires Permutations (a, b)
    ensures |a| == |b|
{ }

// Every sequence is a permutation of itself.

lemma PermReflexive (a : seq<int>)
    ensures Permutations(a, a)
{ }

// If a is a permutation of b then b is a permutation of a.

lemma PermCommutative (a : seq<int>, b : seq<int>)
    requires Permutations(a, b)
    ensures Permutations(b, a)
{ }

// If a is a permutation of b and b is a permutation of c, then a is a
// permutation of c.

lemma PermAssociative (a : seq<int>, b : seq<int>, c : seq<int>)
    requires Permutations(a, b)
    requires Permutations(b, c)
    ensures Permutations(a, c)
{ }

// Concatenating pairs of permutations yields permutations.

lemma PermConcatenation (a1 : seq<int>, a2 : seq<int>, b1 : seq<int>, b2 : seq<int>)
    requires Permutations (a1, a2)
    requires Permutations (b1, b2)
    ensures Permutations (a1+b1, a2+b2)
{ }

