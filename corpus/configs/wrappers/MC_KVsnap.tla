---- MODULE MC_KVsnap ----
(* Hand-authored (no such operator anywhere in the corpus). The cfg's
   SYMMETRY TxIdSymmetric has no matching definition; Permutations(TxId) is
   TLC's standard symmetry-reduction idiom (built into the TLC module) for a
   set with no distinguished elements, which TxId is here. *)
EXTENDS KVsnap, TLC
TxIdSymmetric == Permutations(TxId)
====
