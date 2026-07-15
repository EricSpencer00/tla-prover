---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, orig, work, pc

(* ----------------------------------------------------------------------
   Type definitions
   ---------------------------------------------------------------------- *)

Domain == { [low |-> i, high |-> j] :
              i \in 0 .. MaxSeqLen-1 /\ j \in i .. MaxSeqLen-1 }

(* ----------------------------------------------------------------------
   Helper functions
   ---------------------------------------------------------------------- *)

CountWithin(s, lo, hi, x) ==
    Len({ i \in lo .. hi : s[i] = x })

Sorted(s) ==
    \A i \in 0 .. Len(s)-2 : s[i] <= s[i+1]

Permutation(s, t) ==
    \A x \in Values :
        CountWithin(s, 0, Len(s)-1, x) = CountWithin(t, 0, Len(t)-1, x)

PermutationWithin(s, t, lo, hi) ==
    \A x \in Values :
        CountWithin(s, lo, hi, x) = CountWithin(t, lo, hi, x)

ValidPartition(old, new, interv, p) ==
    /\ \A i \in 0 .. Len(old)-1 :
            (i < interv.low \/ i > interv.high) => new[i] = old[i]
    /\ PermutationWithin(old, new, interv.low, interv.high)
    /\ \A i \in interv.low .. p :
            \A j \in p+1 .. interv.high : new[i] <= new[j]

AllIndices(s) == 0 .. Len(s)-1

DisjointIntervals(ws) ==
    \A a, b \in ws : a # b =>
        (High(a) < Low(b) \/ High(b) < Low(a))

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)

Init ==
    \E s \in Seq :
        Len(s) > 0 /\

        /\ seq = s
        /\ orig = s
        /\ work = { [low |-> 0, high |-> Len(s)-1] }
        /\ pc = Running

(* ----------------------------------------------------------------------
   Next-step action
   ---------------------------------------------------------------------- *)

Next ==
    \/ (pc = Running /\ work # {} /\

        \E interv \in work :
            (interv.low = interv.high /\

             /\ pc' = Running
             /\ work' = work \ {interv}
             /\ seq' = seq
             /\ orig' = orig))

    \/ (pc = Running /\ work # {} /\

        \E interv \in work :
            (interv.low < interv.high /\

             /\ \E p \in interv.low .. interv.high-1 : (
                    /\ \E newSeq \in Seq :
                        ValidPartition(seq, newSeq, interv, p)
                    /\ pc' = Running
                    /\ work' = (work \ {interv}) \cup
                                { [low |-> interv.low, high |-> p],
                                  [low |-> p+1,      high |-> interv.high] }
                    /\ seq' = newSeq
                    /\ orig' = orig)))

    \/ (pc = Running /\ work = {} /\

        /\ pc' = Terminated
        /\ work' = work
        /\ seq' = seq
        /\ orig' = orig)

    \/ (pc = Terminated /\

        /\ pc' = Terminated
        /\ work' = work
        /\ seq' = seq
        /\ orig' = orig)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

vars == {seq, orig, work, pc}

Spec == Init /\ [][Next]_vars

(* ----------------------------------------------------------------------
   Safety invariants
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ seq \in Seq
    /\ orig \in Seq
    /\ work \subseteq Domain
    /\ pc \in {Running, Terminated}

PCorrect ==
    pc = Terminated => Sorted(seq) /\ Permutation(seq, orig)

InvocationInvariant ==
    TypeOK
    /\ Permutation(seq, orig)
    /\ AllIndices(seq) = \u_{interv \in work} { i \in interv.low .. interv.high }
    /\ DisjointIntervals(work)
    /\ \A interv \in work : interv.low < interv.high

(* The module declares the invariants as required by the .cfg file *)
INVARS == TypeOK, PCorrect, InvocationInvariant

(* ----------------------------------------------------------------------
   Liveness property
   ---------------------------------------------------------------------- *)

Termination == <> (pc = Terminated)

====