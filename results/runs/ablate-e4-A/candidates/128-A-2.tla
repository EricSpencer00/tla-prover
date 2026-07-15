---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets

CONSTANTS
    Values,  \* Subset of \Int
    MaxSeqLen,
    Seq

VARIABLES
    SeqVar,  \* current sequence
    OrigSeq, \* original sequence
    WorkSet, \* set of intervals
    PC

(* Simple record representing an interval *)
IsInterval(I) == /\ I \in [low : Nat, high : Nat]
                 /\ I.low <= I.high
                 /\ I.low < MaxSeqLen
                 /\ I.high < MaxSeqLen

InInterval(i, I) == /\ I.low <= i <= I.high

(* Subintervals around a pivot *)
SubIntervals(I, p) == 
    UNION {
        [low |-> I.low, high |-> p] : p >= I.low
      } \cup
    UNION {
        [low |-> p+1, high |-> I.high] : p+1 <= I.high
    }

(* Predicate that a sequence S is a valid partition of Seq over interval I with pivot p *)
ValidPartition(S, Seq, I, p) ==
    /\ S \in Seq                    \* same type
    /\ \A i \in 0..(Len(Seq)-1) :
          IF i \in I THEN
             S[i] \in DOMAIN(Seq)
          ELSE
             S[i] = Seq[i]
    /\ \A i \in I.low..p, j \in (p+1)..I.high :
           S[i] <= S[j]

(* Helper: nondecreasing order *)
Sorted(s) == \A i \in 0..(Len(s)-2) : s[i] <= s[i+1]

(* Initial state *)
Init ==
    /\ SeqVar \in Seq
    /\ LenSeq = Len(SeqVar)
    /\ LenSeq >= 1
    /\ OrigSeq = SeqVar
    /\ WorkSet = {[low |-> 0, high |-> LenSeq-1]}
    /\ PC = "RUN"

(* Main action: process an interval *)
Process ==
    LET I == CHOOSE x \in WorkSet : TRUE
        p == CHOOSE j \in I.low..I.high : TRUE
        NewSeq == CHOOSE s \in Seq : ValidPartition(s, SeqVar, I, p)
        NewWork == (WorkSet \ {I}) \cup SubIntervals(I, p)
    IN
        /\ PC = "RUN"
        /\ WorkSet # {}
        /\ I \in WorkSet
        /\ I.low <= I.high
        /\ I.low = I.high
        /\ SeqVar' = SeqVar
        /\ WorkSet' = WorkSet \ {I}
        /\ PC' = PC
    \/ LET I == CHOOSE x \in WorkSet : TRUE
            p == CHOOSE j \in I.low..I.high : TRUE
            NewSeq == CHOOSE s \in Seq : ValidPartition(s, SeqVar, I, p)
            NewWork == (WorkSet \ {I}) \cup SubIntervals(I, p)
        IN
        /\ PC = "RUN"
        /\ WorkSet # {}
        /\ I \in WorkSet
        /\ I.low < I.high
        /\ SeqVar' = NewSeq
        /\ WorkSet' = NewWork
        /\ PC' = PC

(* Termination action *)
Terminate ==
    /\ PC = "RUN"
    /\ WorkSet = {}
    /\ PC' = "DONE"
    /\ UNCHANGED SeqVar, OrigSeq, WorkSet

(* Stuttering step after termination *)
Stutter ==
    /\ PC = "DONE"
    /\ UNCHANGED SeqVar, OrigSeq, WorkSet, PC

Next == Process \/ Terminate \/ Stutter

Spec == Init /\ [][Next]_<<SeqVar, OrigSeq, WorkSet, PC>>

(* Type correctness invariant *)
TypeOK ==
    /\ SeqVar \in Seq
    /\ OrigSeq \in Seq
    /\ WORKSET_OK
    /\ PC \in {"RUN", "DONE"}

WORKSET_OK ==
    /\ WorkSet \subseteq {[low |-> i, high |-> j] : i \in 0..(MaxSeqLen-1) /\ j \in i..(MaxSeqLen-1)}
    /\ \A I \in WorkSet : IsInterval(I)

(* Global permutation invariant *)
PermInvariant ==
    /\ SORT(SeqVar) = SORT(OrigSeq)

(* PCorrect: when terminated, sequence is sorted and is a permutation of original *)
PCorrect ==
    /\ PC = "DONE"
    /\ Sorted(SeqVar)
    /\ SORT(SeqVar) = SORT(OrigSeq)

Inv == TypeOK /\ PermInvariant

Termination == EVENTUALLY (WorkSet = {})

====