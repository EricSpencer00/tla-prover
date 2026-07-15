---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Constants                                                             *)
(*                                                                        *)
(*  Values   : a finite subset of Nat, supplied by the .cfg                 *)
(*  MaxSeqLen: a positive integer bound on the length of Seq (also from cfg) *)
(*  Seq      : the initial sequence, a function from 1..MaxSeqLen to Values*)
(*                                                                        *)
(*  The .cfg file must provide concrete values for these constants.        *)
(***************************************************************************)

CONSTANTS Values, MaxSeqLen, Seq

(* --------------------------------------------------------------------- *)
(*  Helper definitions                                                   *)
(* --------------------------------------------------------------------- *)

Domain == 1 .. MaxSeqLen

IdxSet == DOMAIN Seq

VARIABLES seq, origSeq, workSet, pc

(* seq     : current working sequence, a function 1..MaxSeqLen -> Values *)
(* origSeq : immutable copy of the initial sequence                     *)
(* workSet : set of intervals (each interval is a pair <<l, u>> with 1<=l<=u<=MaxSeqLen) *)
(* pc      : program counter, either "Running" or "Done"               *)

(* --------------------------------------------------------------------- *)
(*  Intervals                                                             *)
(* --------------------------------------------------------------------- *)

Interval == [l : Nat, u : Nat]   \* l <= u, both in 1..MaxSeqLen

IsSingleton(i) == i.l = i.u

(* --------------------------------------------------------------------- *)
(*  Permutation predicate (bijection on 1..MaxSeqLen)                     *)
(* --------------------------------------------------------------------- *)

Permutation == { f \in [Domain -> Domain] : 
                  \A i, j \in Domain : f[i] = f[j] => i = j }

(* --------------------------------------------------------------------- *)
(*  Sequence permutation under a bijection                               *)
(* --------------------------------------------------------------------- *)

Permute(s, f) == [i \in Domain |-> s[f[i]]]

(* --------------------------------------------------------------------- *)
(*  Valid partition of interval i with pivot p, producing new sequence s' *)
(* --------------------------------------------------------------------- *)

ValidPartition(s, i, p, sPrime) ==
  /\ i.l \in Domain
  /\ i.u \in Domain
  /\ i.l <= i.u
  /\ p \in i.l .. i.u
  /\ \A j \in Domain :
        (j < i.l) \/ (j > i.u) => sPrime[j] = s[j]   \* outside interval unchanged
  /\ \A j \in i.l .. p    : sPrime[j] <= sPrime[p]
  /\ \A j \in p+1 .. i.u : sPrime[p] <= sPrime[j]

(* --------------------------------------------------------------------- *)
(*  Type correctness predicate                                            *)
(* --------------------------------------------------------------------- *)

TypeOK ==
  /\ seq \in [Domain -> Values]
  /\ origSeq \in [Domain -> Values]
  /\ workSet \subseteq SUBSET { [l |-> l, u |-> u] : l, u \in Domain, l <= u }
  /\ pc \in {"Running", "Done"}

(* --------------------------------------------------------------------- *)
(*  Safety invariant: sequence is a permutation of the original          *)
(* --------------------------------------------------------------------- *)

Inv ==
  \E f \in Permutation : seq = Permute(origSeq, f)

(* --------------------------------------------------------------------- *)
(*  Partial correctness: when terminated, seq is sorted and a perm of   *)
(*  origSeq.  This is a derived property rather than the primary invariant*)
(* --------------------------------------------------------------------- *)

PCorrect ==
  /\ pc = "Done"
  /\ \A i, j \in Domain : i < j => seq[i] <= seq[j]
  /\ Inv

(* --------------------------------------------------------------------- *)
(*  Initial state                                                         *)
(* --------------------------------------------------------------------- *)

Init ==
  /\ seq = Seq
  /\ origSeq = Seq
  /\ workSet = { [l |-> 1, u |-> MaxSeqLen] }
  /\ pc = "Running"

(* --------------------------------------------------------------------- *)
(*  Main loop actions                                                     *)
(* --------------------------------------------------------------------- *)

LoopStep ==
  \/ /\ pc = "Running"
        /\ workSet # {}
        /\ \E i \in workSet :
            /\ (i.l = i.u)               \* singleton interval
               /\ workSet' = workSet \ {i}
               /\ UNCHANGED <<seq, origSeq, pc>>
            \/ /\ i.l < i.u               \* need to partition
               /\ \E p \in i.l .. i.u :
                   /\ \E sPrime \in [Domain -> Values] :
                        /\ ValidPartition(seq, i, p, sPrime)
                        /\ seq' = sPrime
                        /\ workSet' = (workSet \ {i}) \cup {
                              [l |-> i.l, u |-> p],
                              [l |-> p+1, u |-> i.u]
                            }
                        /\ pc' = "Running"
        /\ UNCHANGED origSeq
  \/ /\ pc = "Running"
        /\ workSet = {}
        /\ pc' = "Done"
        /\ UNCHANGED <<seq, origSeq, workSet>>
  \/ /\ pc = "Done"
        /\ UNCHANGED <<seq, origSeq, workSet, pc>>

Next == LoopStep

(* --------------------------------------------------------------------- *)
(*  Specification                                                         *)
(* --------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<seq, origSeq, workSet, pc>>

(* --------------------------------------------------------------------- *)
(*  Stuttering step after termination (already covered in LoopStep)      *)
(* --------------------------------------------------------------------- *)

=============================================================================