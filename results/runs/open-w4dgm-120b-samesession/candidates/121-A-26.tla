---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* A zero-indexed sequence of characters drawn from a finite character set.
\* The failure function is an array indexed into the doubled string.
\* The program counter (pc) drives the algorithm through its labeled steps.
VARIABLES input, n, failure, pi, k, best, pc

vars == <<input, n, failure, pi, k, best, pc>>

Sentinel == 0 - 1

TypeInvariant ==
    /\ input \in [1..n -> CharacterSet]
    /\ n \in Nat
    /\ failure \in [0..(2 * n) -> (0..(2 * n)) \cup {Sentinel}]
    /\ pi \in (0..(2 * n)) \cup {Sentinel}
    /\ k \in 0..(2 * n)
    /\ best \in 0..(n - 1)
    /\ pc \in {"outer", "lookup", "inner", "follow", "post", "done"}

Init ==
    /\ \E s \in [1..n -> CharacterSet] : input = s
    /\ n \in Nat
    /\ failure = [i \in 0..(2 * n) |-> Sentinel]
    /\ pi = Sentinel
    /\ k = 1
    /\ best = 0
    /\ pc = "outer"

\* The outer loop runs up to twice the string length (the doubled string)
\* so the circular wrap-around is handled without special case arithmetic.
Outer ==
    /\ pc = "outer"
    /\ k < (2 * n)
    /\ pc' = "lookup"
    /\ UNCHANGED <<input, n, failure, pi, k, best>>

Lookup ==
    /\ pc = "lookup"
    /\ pi' = failure[k - 1]
    /\ pc' = "inner"
    /\ UNCHANGED <<input, n, failure, k, best>>

\* Compare the doubled-string character at k (mod n) with the candidate
\* rotation character at (best + k) (mod n); follow the failure link if
\* the pattern-match index (pi) is set, otherwise exit the inner loop.
Inner ==
    /\ pc = "inner"
    /\ \/ (input[(k % n) + 1] # input[((best + k) % n) + 1] /\ pi # Sentinel)
       \/ (pi = Sentinel)
    /\ pc' \in IF (input[(k % n) + 1] # input[((best + k) % n) + 1] /\ pi # Sentinel)
                  THEN {"post", "follow"} ELSE {"post"}
    /\ UNCHANGED <<input, n, failure, pi, k, best>>

\* If the current character is smaller than the candidate's, this rotation
\* is a better lexicographic match.
Update ==
    /\ input[(k % n) + 1] < input[((best + k) % n) + 1]
    /\ best' = k % n
    /\ UNCHANGED <<input, n, failure, pi, k, pc>>

Follow ==
    /\ pc = "follow"
    /\ pi' = failure[pi]
    /\ pc' \in IF (input[(k % n) + 1] # input[((best + k) % n) + 1] /\ pi # Sentinel)
                  THEN {"post", "follow"} ELSE {"post"}
    /\ UNCHANGED <<input, n, failure, k, best>>

Post ==
    /\ pc = "post"
    /\ \/ (input[(k % n) + 1] # input[((best + k) % n) + 1] /\ pi = Sentinel)
       \/ (input[(k % n) + 1] = input[((best + k) % n) + 1])
    /\ failure' = [failure EXCEPT ![k] = IF pi = Sentinel THEN Sentinel ELSE pi + 1]
    /\ pi' = Sentinel
    /\ pc' = "done"
    /\ UNCHANGED <<input, n, k, best>>

Done ==
    /\ pc = "done"
    /\ k' = k + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<input, n, failure, pi, best>>

Stutter ==
    /\ pc = "done"
    /\ k >= (2 * n)
    /\ UNCHANGED vars

Next ==
    \/ Outer \/ Lookup \/ Inner \/ Update \/ Follow \/ Post \/ Done \/ Stutter

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Outer) /\ WF_vars(Lookup) /\ WF_vars(Inner)
    /\ WF_vars(Post) /\ WF_vars(Done)

\* Upon termination, the rotation at offset 'best' is lexicographically
\* less than or equal to every other rotation of the input string.
Correctness ==
    /\ k >= (2 * n)
    /\ \A i \in 0..(n - 1) :
         /\ Subseq(input, ((best) % n) + 1, n) <= Subseq(input, ((i) % n) + 1, n)
         /\ (Subseq(input, ((best) % n) + 1, n) = Subseq(input, ((i) % n) + 1, n)
               => (best % n) <= (i % n))

Termination ==
    (\A e \in vars : e # {}) ~> (k >= (2 * n))

\* The model-checking configuration replaces Naturals with a bounded
\* finite version (CharacterSet is a subset of Nat) so finite-model checking
\* applies; the operators below are defined here and must NOT be redeclared.
CharacterSet == CharacterSet

====