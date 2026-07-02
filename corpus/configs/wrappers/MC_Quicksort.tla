---- MODULE MC_Quicksort ----
(* Hand-authored (no upstream/sibling wrapper found). Same fix as
   MC_BinarySearch.tla -- the cfg substitutes Seq <- LimitedSeq bounded by
   MaxSeqLen. *)
EXTENDS Quicksort
CONSTANT MaxSeqLen
LimitedSeq(S) == UNION {[1..n -> S] : n \in 0..MaxSeqLen}
====
