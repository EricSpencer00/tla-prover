---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

(* -------------------------------------------------------------------- *)
(*  LimitedSeq replaces the unbounded Seq operator from Sequences.       *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

VARIABLES seq, orig, workset, pc

(* -------------------------------------------------------------------- *)
(*  Helper definitions *)

Idx == Nat
Interval == <<Idx, Idx>>

IsInterval(I) ==
    /\ I[1] \in Nat
    /\ I[2] \in Nat
    /\ I[1] <= I[2]
    /\ I[2] <= Len(seq)

(* -------------------------------------------------------------------- *)
(*  Type correctness invariant                                            *)

TypeOK ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ workset \subseteq { I \in Interval : IsInterval(I) }
    /\ pc \in {"Loop", "Done"}

(* -------------------------------------------------------------------- *)
(*  Initial state *)

Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ workset = { <<1, Len(seq)>> }
    /\ pc = "Loop"

(* -------------------------------------------------------------------- *)
(*  Sortedness and permutation predicates *)

Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Permutes(s, t) ==
    /\ Len(s) = Len(t)
    /\ \A v \in Values : Count(s, v) = Count(t, v)

(* -------------------------------------------------------------------- *)
(*  Partition operator: all sequences that are a valid result of a       *)
(*  partition of interval [l..h] around pivot p.                         *)

Partition(old, l, h, p) ==
    { new \in Seq(Values) :
        /\ Len(new) = Len(old)
        /\ \A i \in 1..Len(old) :
               (i < l \/ i > h) => new[i] = old[i]
        /\ \A i \in l..p, j \in (p+1)..h : new[i] <= new[j]
        /\ \A v \in Values :
               Count(old[l..h], v) = Count(new[l..h], v) }

(* -------------------------------------------------------------------- *)
(*  Main transition relation                                            *)

Next ==
    \/ /\ pc = "Loop"
       /\ workset # {}
       /\ \E I \in workset :
            LET l == I[1] IN
            LET h == I[2] IN
            IF l = h THEN
               /\ seq' = seq
               /\ orig' = orig
               /\ workset' = workset \ {I}
               /\ pc' = "Loop"
            ELSE
               /\ \E p \in l..h :
                    /\ \E newSeq \in Partition(seq, l, h, p) :
                         /\ seq' = newSeq
                         /\ orig' = orig
                         /\ workset' = (workset \ {I}) \cup { <<l, p>>, <<p+1, h>> }
                         /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ workset = {}
       /\ seq' = seq
       /\ orig' = orig
       /\ workset' = workset
       /\ pc' = "Done"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<seq, orig, workset, pc>>

(* -------------------------------------------------------------------- *)
(*  Invariants                                                          *)

PCorrect ==
    /\ pc = "Done" => Sorted(seq) /\ Permutes(seq, orig)

Inv ==
    TypeOK /\ (pc = "Loop" => TRUE)

(* -------------------------------------------------------------------- *)
(*  Specification                                                       *)

Spec == Init /\ [][Next]_<<seq, orig, workset, pc>>

(* -------------------------------------------------------------------- *)
(*  Liveness property (termination)                                     *)

Termination == <> (pc = "Done")

====