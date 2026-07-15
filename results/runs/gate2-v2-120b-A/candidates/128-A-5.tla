---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(*  CONSTANTS                                                            *)
(***************************************************************************)
CONSTANTS Values, MaxSeqLen, Seq

(***************************************************************************)
(*  Helper definitions                                                   *)
(***************************************************************************)

Idx == 1 .. MaxSeqLen

(* The input sequence is a function from indices to values, undefined beyond its length *)
SeqInit == [i \in Idx |-> IF i <= Len(Seq) THEN Seq[i] ELSE Values[1]]

(* The set of all intervals (contiguous ranges) over the index domain *)
Interval == { [low |-> l, high |-> h] : l, h \in Idx /\ l <= h }

(* Permutation of a sequence: a bijection on the index set that preserves values *)
Permute(s, f) == [i \in Idx |-> s[f[i]]]
Bijective(f) == (f \in [Idx -> Idx]) /\ (\A i \in Idx: (\E j \in Idx: f[j] = i))

(***************************************************************************)
(*  Variables                                                            *)
(***************************************************************************)
VARIABLES s, s0, work, pc

(***************************************************************************)
(*  Initial state                                                        *)
(***************************************************************************)
Init ==
    /\ s = SeqInit
    /\ s0 = SeqInit
    /\ work = { [low |-> 1, high |-> Len(Seq)] }
    /\ pc = "Loop"

(***************************************************************************)
(*  Partition operation (abstracted)                                      *)
(***************************************************************************)
Partition(s, intv, pivot) ==
    LET low == intv.low IN
    LET high == intv.high IN
    LET left  == 1 .. (pivot - 1) IN
    LET right == pivot .. high IN
    \E f \in [Idx -> Idx]:
        /\ Bijective(f)
        /\ (\A i \in Idx \ {pivot} :
                (i \in low..high) => 
                    IF i \in left THEN s[f[i]] <= s[pivot] ELSE s[f[i]] >= s[pivot])
        /\ (\A i \in Idx \ (low..high) : f[i] = i)
        /\ s' = [j \in Idx |-> IF j \in low..high THEN s[f[j]] ELSE s[j]]
    /\ s'

(***************************************************************************)
(*  Next-state relation                                                   *)
(***************************************************************************)
Next ==
    \/ /\ pc = "Loop"
       /\ work # {}
       /\ \E intv \in work:
            LET low == intv.low IN
            LET high == intv.high IN
            IF low = high THEN
                /\ s' = s
                /\ work' = work \ {intv}
                /\ pc' = "Loop"
            ELSE
                /\ \E pivot \in low..high:
                    /\ s' \in Partition(s, intv, pivot)
                    /\ work' = (work \ {intv}) \cup {
                            [low |-> low, high |-> pivot - 1],
                            [low |-> pivot, high |-> high]
                        }
                    /\ pc' = "Loop"
    \/ /\ pc = "Loop"
       /\ work = {}
       /\ s' = s
       /\ s0' = s0
       /\ work' = work
       /\ pc' = "Done"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<s, s0, work, pc>>

Spec == Init /\ [][Next]_<<s, s0, work, pc>>

(***************************************************************************)
(*  Types for TLC                                                       *)
(***************************************************************************)
TypeOK ==
    /\ s \in [Idx -> Values]
    /\ s0 \in [Idx -> Values]
    /\ work \subseteq Interval
    /\ pc \in {"Loop", "Done"}

(***************************************************************************)
(*  Inductive invariant (domain partition, permutation, sortedness)     *)
(***************************************************************************)
Sorted(seq) ==
    \A i, j \in Idx : (i < j) => seq[i] <= seq[j]

Inv ==
    /\ TypeOK
    /\ \A i \in Idx : s[i] = s0[i] \/ (i \in UNION { intv.low .. intv.high : intv \in work })
    /\ s \in Permutations(s0)   \* permutation preservation (abstract)

PCorrect ==
    /\ pc = "Done"
    /\ Sorted(s)
    /\ \A i \in Idx : s[i] = s0[i]

Termination ==
    <> (pc = "Done")

=============================================================================