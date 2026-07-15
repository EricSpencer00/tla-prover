---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, TLC

(*-------------------------------------------------------------------*)
(*  Constants (to be instantiated in the .cfg)                        *)
(*-------------------------------------------------------------------*)
CONSTANT Nodes
CONSTANT Root
CONSTANT Succ
CONSTANT Seq

(*-------------------------------------------------------------------*)
(*  Derived sets and functions                                        *)
(*-------------------------------------------------------------------*)
NodeSet == Nodes

(* Succ is a total function from each node to a set of exactly two
   distinct successor nodes.  The .cfg must assign such a function. *)
Succs == [n \in NodeSet |-> Succ[n]]

(* A finite sequence of nodes is represented by the built‑in
   sequence type.  The bound on its length is enforced by a helper
   predicate below.                                          *)
Bound == Cardinality(NodeSet)

IsBoundedSeq(s) == Len(s) <= Bound

(*-------------------------------------------------------------------*)
(*  State variables                                                   *)
(*-------------------------------------------------------------------*)
VARIABLES marked, frontier, pc, seqs

(*-------------------------------------------------------------------*)
(*  Type definitions                                                  *)
(*-------------------------------------------------------------------*)
Node == NodeSet
SeqOfNodes == Seq \* the abstract identifier required by the .cfg

(*-------------------------------------------------------------------*)
(*  Helper predicates                                                 *)
(*-------------------------------------------------------------------*)
IsMarkedSet(M) == M \subseteq NodeSet
IsFrontierSet(F) == F \subseteq NodeSet

IsSeqSet(S) == S \subseteq SeqOfNodes /\ \A s \in S : IsBoundedSeq(s)

IsNextSeq(s) == 
  \E n \in NodeSet : 
    Len(s) < Bound /\ s \cat <<n>> \in SeqOfNodes /\ IsBoundedSeq(s \cat <<n>>)

(*-------------------------------------------------------------------*)
(*  Initial predicate                                                 *)
(*-------------------------------------------------------------------*)
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "Loop"
  /\ seqs = { <<Root>> }

(*-------------------------------------------------------------------*)
(*  Next-state relation                                               *)
(*-------------------------------------------------------------------*)
Next ==
  \/ /\ pc = "Loop"
     /\ frontier # {}
     /\ \E n \in frontier :
          /\ marked' = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup (Succs[n] \ marked)
          /\ pc' = "Loop"
          /\ seqs' = seqs
  \/ /\ pc = "Loop"
     /\ frontier = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<marked, frontier, seqs>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<marked, frontier, seqs, pc>>

(*-------------------------------------------------------------------*)
(*  Specification                                                    *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<marked, frontier, pc, seqs>>

(*-------------------------------------------------------------------*)
(*  Invariants                                                       *)
(*-------------------------------------------------------------------*)
TypeOK ==
  /\ IsMarkedSet(marked)
  /\ IsFrontierSet(frontier)
  /\ IsSeqSet(seqs)
  /\ pc \in {"Loop", "Done"}

Inv1 == (* successor closure *)
  \A n \in marked : \A s \in Succs[n] : s \in marked \/ s \in frontier

Inv2 == (* reachability decomposition: nodes are either reached or still
          in the frontier, and no node is both *)
  \A n \in NodeSet : (n \in marked) \/ (n \in frontier)

Inv3 == (* reachable set equality: every node reachable from Root
          via a bounded sequence is eventually in marked *)
  \A n \in NodeSet :
    (\E s \in seqs : Len(s) > 0 /\ s[1] = Root /\ s[Len(s)] = n) => n \in marked

PartialCorrectness == (* when algorithm terminates, all reachable nodes are marked *)
  pc = "Done" => marked = { n \in NodeSet : \E s \in seqs : s[1] = Root /\ s[Len(s)] = n }

(*-------------------------------------------------------------------*)
(*  Liveness property                                                 *)
(*-------------------------------------------------------------------*)
Termination == <> (pc = "Done")

=============================================================================