---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet, Nat

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* The input string is a sequence indexed from 0 (zero‑indexed)
InputString == [i \in Nat |-> CharacterSet]

\* Length of the input string
StringLength == Nat

\* Failure function maps indices 0..2*StringLength to either a valid
\* index in 0..StringLength or the sentinel value.
FailureFun == [i \in 0..2*StringLength |-> (Sentinel \cup 0..StringLength)]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES s, n, f, i, k, r, pc

\* ----------------------------------------------------------------------
\* Initialization (the nondeterministic choice of the input string)
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ s \in [0..n-1 -> CharacterSet]
  /\ f = [j \in 0..2*n |-> Sentinel]
  /\ i = Sentinel
  /\ k = 1
  /\ r = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Helper to obtain a character modulo the string length
\* ----------------------------------------------------------------------
Char(pos) == s[ pos % n ]

\* ----------------------------------------------------------------------
\* Actions corresponding to the labeled steps of Booth's algorithm
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF k < 2 * n
        THEN /\ pc' = "Lookup"
        ELSE /\ pc' = "Done"
  /\ UNCHANGED << s, n, f, i, k, r >>

Lookup ==
  /\ pc = "Lookup"
  /\ fPos = (k - r) % n
  /\ i' = f[fPos]
  /\ pc' = "InnerComp"
  /\ UNCHANGED << s, n, f, k, r >>

InnerComp ==
  /\ pc = "InnerComp"
  /\ IF i' # Sentinel /\ Char(i' + r) # Char(k % n)
        THEN /\ pc' = "FollowFailure"
        ELSE IF i' = Sentinel \/ Char(i' + r) # Char(k % n)
                THEN /\ pc' = "PostComp"
                ELSE /\ i' = i' + 1
                     /\ pc' = "InnerComp"
  /\ UNCHANGED << s, n, f, k, r >>

FollowFailure ==
  /\ pc = "FollowFailure"
  /\ i' = f[i']
  /\ pc' = "InnerComp"
  /\ UNCHANGED << s, n, f, k, r >>

PostComp ==
  /\ pc = "PostComp"
  /\ IF i' = Sentinel \/ Char(i' + r) # Char(k % n)
        THEN /\ IF Char(k % n) < Char(i' + r)
                THEN /\ r' = k % n
                ELSE /\ r' = r
        ELSE /\ r' = r
  /\ f' = [j \in DOMAIN f |-> 
          IF j = (k - r) % n
             THEN IF i' = Sentinel
                     THEN Sentinel
                     ELSE i' + 1
             ELSE f[j]]
  /\ k' = k + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << s, n, i >>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED << s, n, f, i, k, r, pc >>

\* ----------------------------------------------------------------------
\* Stuttering step to allow the model to remain in the final state
\* ----------------------------------------------------------------------
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED << s, n, f, i, k, r, pc >>

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerComp
  \/ FollowFailure
  \/ PostComp
  \/ Done
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<s, n, f, i, k, r, pc>>

\* ----------------------------------------------------------------------
\* Type invariant (required by the configuration file)
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ s \in [0..n-1 -> CharacterSet]
  /\ f \in [0..2*n -> (Sentinel \cup 0..n)]
  /\ i \in Sentinel \cup 0..n
  /\ k \in Nat /\ 1 <= k /\ k <= 2*n + 1
  /\ r \in 0..n-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerComp", "FollowFailure",
            "PostComp", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant: r always points to the lexicographically
\* smallest rotation seen so far, and upon termination it is the
\* minimal rotation of the whole string.
\* ----------------------------------------------------------------------
Correctness ==
  /\ \A j \in 0..n-1 :
        LexLessOrEqual(Rotate(s, r), Rotate(s, j))

\* Lexicographic comparison of two zero‑indexed sequences
LexLessOrEqual(u, v) ==
  \E m \in 0..n :
    /\ \A l \in 0..m-1 : u[l] = v[l]
    /\ (m = n \/ u[m] <= v[m])

\* Rotation of a zero‑indexed sequence by offset o
Rotate(seq, o) ==
  [j \in 0..n-1 |-> seq[(j + o) % n]]

\* ----------------------------------------------------------------------
\* The names required by the .cfg file
\* ----------------------------------------------------------------------
\* The configuration expects the constant Nat to be the set of natural numbers.
\* We expose it as an operator of the same name.
Nat == Nat

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====