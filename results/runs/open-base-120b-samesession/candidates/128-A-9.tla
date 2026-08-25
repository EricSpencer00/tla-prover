---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Operator that restricts the set of sequences to a bounded length.
\* (Replaces Seq from the Sequences module for model checking.)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsInterval(i) ==
    /\ i \in Seq(Nat)
    /\ Len(i) = 2
    LET l == i[1] , u == i[2] IN
       /\ 1 <= l
       /\ l <= u
       /\ u <= Len(seq)

INTERVALS == { i \in Seq(Nat) : Len(i) = 2 /\ 
                LET l == i[1] , u == i[2] IN 1 <= l /\ l <= u /\ u <= Len(seq) }

IsSorted(s) ==
    /\ Len(s) = 0 \/ Len(s) = 1
    \/ \A i \in 1..Len(s)-1 : s[i] <= s[i+1]

IsBijective(f, dom, ran) ==
    /\ DOMAIN f = dom
    /\ RANGE f = ran
    /\ \A i,j \in dom : f[i] = f[j] => i = j

Permutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \E f \in [1..Len(s1) -> 1..Len(s2)] :
          IsBijective(f, 1..Len(s1), 1..Len(s2))
          /\ \A i \in 1..Len(s1) : s1[i] = s2[f[i]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ seq # <<>>
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Transition relation
\* ----------------------------------------------------------------------
ChooseAndProcess ==
    /\ pc = "Run"
    /\ work # {}
    /\ \E i \in work :
          LET l == i[1] , u == i[2] IN
          IF l = u THEN
              /\ work' = work \ {i}
              /\ UNCHANGED <<seq, orig, pc>>
          ELSE
              /\ \E p \in l..u :
                     \E newSeq \in LimitedSeq(Values) :
                         /\ Len(newSeq) = Len(seq)
                         /\ \A j \in 1..Len(seq) :
                               (j < l \/ j > u) => newSeq[j] = seq[j]
                         /\ \A j \in l..p :
                               \A k \in p+1..u : newSeq[j] <= newSeq[k]
                         /\ \E f \in [l..u -> l..u] :
                               IsBijective(f, l..u, l..u) /\ 
                               \A j \in l..u : newSeq[j] = seq[f[j]]
                         /\ seq' = newSeq
                         /\ work' = (work \ {i}) \cup { <<l,p>>, <<p+1,u>> }
                         /\ UNCHANGED orig
                         /\ UNCHANGED pc

Terminate ==
    /\ pc = "Run"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

StutterAfterDone ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

Next == ChooseAndProcess \/ Terminate \/ StutterAfterDone

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_{<<seq, orig, work, pc>>} /\ WF_{<<seq, orig, work, pc>>}(Next)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ Len(seq) = Len(orig)
    /\ work \subseteq INTERVALS

\* ----------------------------------------------------------------------
\* Main invariant (permutation preservation)
\* ----------------------------------------------------------------------
Inv == TypeOK /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness condition
\* ----------------------------------------------------------------------
PCorrect ==
    (pc = "Done") => (IsSorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====