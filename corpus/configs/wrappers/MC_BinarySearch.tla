---- MODULE MC_BinarySearch ----
(* Hand-authored (no upstream/sibling wrapper found). The cfg substitutes
   Seq <- LimitedSeq bounded by MaxSeqLen -- same bounded-sequence technique
   already used for spec 119's MCFindHighest (MCSeq(S) == UNION {[1..n -> S]
   : n \in Nat}), here bounded to 0..MaxSeqLen instead of all of Nat so TLC
   can actually enumerate it. *)
EXTENDS BinarySearch
CONSTANT MaxSeqLen
LimitedSeq(S) == UNION {[1..n -> S] : n \in 0..MaxSeqLen}
====
