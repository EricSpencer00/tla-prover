---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS CharacterSet, Nat

\* ----------------------------------------------------------------------
\* Definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* A zero-indexed string: a function from 0..Len-1 to characters.
\* We'll model it as a sequence (which is one-indexed) but treat the
\* first element as position 0.
Str == [i \in 0..Len-1 |-> CharacterSetElements[i]]

\* Helper to convert a sequence (one‑indexed) to zero‑indexed mapping.
SeqToZero(seq) ==
    [i \in 0..Len-1 |-> seq[i+1]]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Input, Len, Failure, PatIdx, i, Best

\* The program counter is implicit: the NEXT relation encodes the
\* stepwise execution of the algorithm.
\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Len \in 1..Nat
    /\ Input \in 0..Len-1 -> CharacterSet
    /\ Failure = [j \in 0..2*Len-1 |-> Sentinel]
    /\ PatIdx = Sentinel
    /\ i = 1
    /\ Best = 0

\* ----------------------------------------------------------------------
\* Next-state relation implementing the algorithm
\* ----------------------------------------------------------------------
OuterContinue ==
    i < 2*Len

\* The character at a circular position pos (zero‑indexed)
CharAt(pos) == Input[pos % Len]

\* One iteration of the outer loop
OuterStep ==
    /\ i < 2*Len
    /\ LET cur == CharAt(i) IN
       LET cand == CharAt(Best + i) IN
       IF cur = cand THEN
          /\ i' = i + 1
          /\ PatIdx' = PatIdx
          /\ Failure' = Failure
          /\ Best' = Best
       ELSE
          IF PatIdx # Sentinel /\ CharAt(PatIdx) = cand THEN
             /\ Best' = Best
          ELSE
             /\ IF cur < cand THEN Best' = i ELSE Best' = Best
          /\ Failure' = [Failure EXCEPT ![Best + i] = PatIdx]
          /\ PatIdx' = IF PatIdx = Sentinel THEN Sentinel
                       ELSE Failure[PatIdx]
          /\ i' = i + 1

Termination ==
    /\ i >= 2*Len
    /\ UNCHANGED <<Input, Len, Failure, PatIdx, i, Best>>

Next ==
    \/ (i < 2*Len) /\ OuterStep
    \/ Termination

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Input, Len, Failure, PatIdx, i, Best>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ Len \in 1..Nat
    /\ Input \in 0..Len-1 -> CharacterSet
    /\ Failure \in [j \in 0..2*Len-1 -> (Sentinel \cup 0..2*Len-1)]
    /\ PatIdx \in SentLeftSentinel \cup 0..2*Len-1
    /\ i \in Nat
    /\ Best \in 0..Len-1

\* Helper: rotation of Input by offset k
Rotation(k) ==
    << Input[(j + k) % Len] : j \in 0..Len-1 >>

Correctness ==
    \A k \in 0..Len-1 :
        Rotation(Best) <=_lex Rotation(k)

\* Lexicographic ordering (finite sequences)
_<=_lex ==
    [s, t \in Seq(CharacterSet)] ->
        \A n \in 0..Len :
            (\A j \in 0..n-1 : s[j] = t[j]) /\ (n = Len \/ s[n] <= t[n])

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
TerminationProp == <> Termination

=============================================================================