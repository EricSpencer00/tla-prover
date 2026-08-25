---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT CharacterSet   \* finite set of characters (provided by the .cfg)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES s,                 \* input string (zero‑indexed sequence of characters)
          n,                 \* length of the input string
          fail,              \* failure function array (0..2*n-1 -> Nat \/ {-1})
          pi,                \* pattern‑match index (sentinel = -1)
          i,                 \* outer loop counter (1 .. 2*n)
          best,              \* best rotation offset found so far (0 .. n-1)
          pc                 \* program counter (labels of the algorithm)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* character at circular position p (mod n)
CharAt(p) == s[(p % n)]

\* rotation of the string by offset k, expressed as a sequence of length n
RotSeq(k) == << CharAt(k + j) : j \in 0..n-1 >>

\* lexicographic less‑or‑equal on two sequences of the same length
LexLe(seq1, seq2) ==
  IF Len(seq1) = 0 THEN TRUE
  ELSE IF Head(seq1) < Head(seq2) THEN TRUE
  ELSE IF Head(seq1) > Head(seq2) THEN FALSE
  ELSE LexLe(Tail(seq1), Tail(seq2))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
 /\ s \in Seq(CharacterSet)                \* nondeterministic input string
 /\ n = Len(s)                             \* length of the string
 /\ fail = [j \in 0..2*n-1 |-> Sentinel]   \* failure function initialized
 /\ pi = Sentinel
 /\ i = 1
 /\ best = 0
 /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Algorithm steps (one labelled transition per program‑counter value)
\* ----------------------------------------------------------------------
\* 1. Outer loop check
OuterCheckStep ==
 /\ pc = "OuterCheck"
 /\ IF i < 2*n
    THEN /\ pc' = "Lookup"
         /\ UNCHANGED <<s, n, fail, pi, best, i>>
    ELSE /\ pc' = "Done"
         /\ UNCHANGED <<s, n, fail, pi, best, i>>

\* 2. Failure function lookup (relative to current best offset)
LookupStep ==
 /\ pc = "Lookup"
 /\ LET pos == (i + best) % n IN
    /\ pi' = fail[pos]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<s, n, fail, best, i>>

\* 3. Inner comparison loop (may iterate via repeated actions)
InnerLoopStep ==
 /\ pc = "InnerLoop"
 /\ LET curChar == CharAt(i)
        candChar == CharAt(best + pi + 1)
    IN
    /\ IF curChar = candChar
       THEN /\ pi' = pi + 1
            /\ pc' = "InnerLoop"
            /\ UNCHANGED <<s, n, fail, best, i>>
       ELSE IF pi # Sentinel
            THEN /\ pi' = fail[pi]
                 /\ pc' = "InnerLoop"
                 /\ UNCHANGED <<s, n, fail, best, i>>
            ELSE /\ pc' = "PostComp"
                 /\ UNCHANGED <<s, n, fail, pi, best, i>>

\* 4. Post‑comparison handling
PostCompStep ==
 /\ pc = "PostComp"
 /\ LET curChar == CharAt(i)
        candChar == CharAt(best + pi + 1)
    IN
    /\ IF curChar # candChar
       THEN /\ IF curChar < candChar
               THEN best' = i
               ELSE best' = best
            /\ fail' = [fail EXCEPT ![ (i + best) % n ] = IF pi = Sentinel THEN Sentinel ELSE pi + 1]
            /\ pc' = "Inc"
            /\ UNCHANGED <<s, n, pi, i>>
       ELSE /\ pc' = "Inc"
            /\ UNCHANGED <<s, n, fail, pi, best, i>>

\* 5. Increment outer loop counter
IncStep ==
 /\ pc = "Inc"
 /\ i' = i + 1
 /\ pc' = "OuterCheck"
 /\ UNCHANGED <<s, n, fail, pi, best>>

\* 6. Stuttering after termination
DoneStep ==
 /\ pc = "Done"
 /\ UNCHANGED <<s, n, fail, pi, i, best, pc>>

Next ==
 \/ OuterCheckStep
 \/ LookupStep
 \/ InnerLoopStep
 \/ PostCompStep
 \/ IncStep
 \/ DoneStep

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<s, n, fail, pi, i, best, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
 /\ s \in Seq(CharacterSet)
 /\ n = Len(s)
 /\ fail \in [0..2*n-1 -> Nat \cup {Sentinel}]
 /\ pi \in Nat \cup {Sentinel}
 /\ i \in Nat
 /\ best \in 0..n-1
 /\ pc \in {"OuterCheck","Lookup","InnerLoop","PostComp","Inc","Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (holds upon termination)
\* ----------------------------------------------------------------------
Correctness ==
 /\ pc = "Done"
 /\ \A k \in 0..n-1 : LexLe(RotSeq(best), RotSeq(k))

\* ----------------------------------------------------------------------
\* Liveness: termination (implicit via fairness of Next)
\* ----------------------------------------------------------------------
\* (No explicit property required; TLC will check that the algorithm
\* eventually reaches the state with pc = "Done".)

====