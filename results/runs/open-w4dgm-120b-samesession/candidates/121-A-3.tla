---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* The classic Booth algorithm for the lexicographically-least circular
\* rotation of a string, modeled as a single sequential loop without
\* concurrency. The input string is chosen nondeterministically from all
\* character sequences over the finite alphabet CharacterSet.
\* Compared to the paper: the inner loop below has been restructured so
\* that the failure-function lookup is a separate step (the "Lookup" action)
\* and the failure-function update happens only once per outer iteration
\* (the "Follow" action), which is what keeps the failure function bounded
\* to valid indices instead of growing unboundedly.

VARIABLES str, n, fail, pi, i, best, pc
vars == <<str, n, fail, pi, i, best, pc>>

Sentinel == n + 1

TypeInvariant ==
  /\ str \in [1..n -> CharacterSet]
  /\ n \in Nat
  /\ fail \in [0..2*n -> 0..Sentinel]
  /\ pi \in 0..Sentinel
  /\ i \in Nat
  /\ best \in 0..(n - 1)

Init ==
  /\ \E s \in CharacterSet : \E len \in Nat :
       /\ str = [k \in 1..len |-> s]
       /\ n = len
  /\ fail = [k \in 0..(2*n) |-> Sentinel]
  /\ pi = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* Outer loop: runs up to twice the string length to cover the doubled
\* virtual string that handles wrap-around; terminates at the end.
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
       THEN pc' = "Lookup"
       ELSE pc' = "Terminated"
  /\ UNCHANGED <<str, n, fail, pi, i, best>>

\* Failure function lookup: reads the precomputed failure value for the
\* current position relative to the current best offset.
Lookup ==
  /\ pc = "Lookup"
  /\ pi' = fail[(i - 1) % n]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, i, best>>

\* Inner loop: compare the character at the current position (mod n) with
\* the character at the candidate position (mod n). If they differ and a
\* failure link is recorded, continue looping; otherwise fall through.
InnerLoop ==
  /\ pc = "InnerLoop"
  /\ IF str[i % n + 1] = str[(best + i) % n + 1]
       THEN pc' = "Follow"
       /\ pi' = Sentinel
       /\ UNCHANGED <<best>>
       ELSE IF pi # Sentinel
            THEN pc' = "InnerLoop"
                 /\ pi' = fail[pi - 1]
                 /\ UNCHANGED <<best>>
            ELSE pc' = "PostCompare"
                 /\ UNCHANGED <<best, pi>>
  /\ UNCHANGED <<str, n, fail, i>>

\* Update the best offset if the current character is strictly smaller
\* than the candidate character.
Update ==
  /\ pc = "Update"
  /\ best' = i
  /\ pc' = "Follow"
  /\ UNCHANGED <<str, n, fail, pi, i>>

\* Follow the failure function chain: record the next failure function
\* entry for the current outer-loop position, either resetting it or
\* extending it by one past the matched prefix.
Follow ==
  /\ pc = "Follow"
  /\ fail' = [fail EXCEPT ![i % n] = IF pi = Sentinel THEN Sentinel ELSE pi + 1]
  /\ pc' = "Inc"
  /\ UNCHANGED <<str, n, pi, i, best>>

\* Post-comparison step when the inner loop exhausted its failure chain
\* without finding a match: update the best offset if the current
\* character is smaller (a strict improvement), then record the reset.
PostCompare ==
  /\ pc = "PostCompare"
  /\ IF str[i % n + 1] < str[(best + i) % n + 1]
       THEN best' = i
       /\ fail' = [fail EXCEPT ![i % n] = Sentinel]
       /\ pc' = "Inc"
       /\ UNCHANGED <<str, n, pi, i>>
       ELSE fail' = [fail EXCEPT ![i % n] = Sentinel]
            /\ pc' = "Inc"
            /\ UNCHANGED <<str, n, pi, i, best>>

\* Loop counter increment and return to the outer check.
Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, pi, best>>

\* Stuttering in the final state after termination.
Stall ==
  /\ pc = "Terminated"
  /\ UNCHANGED vars

Terminated == pc = "Terminated"

Next ==
  \/ OuterCheck \/ Lookup \/ InnerLoop \/ Update
  \/ Follow \/ PostCompare \/ Inc \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Inc)

\* Correctness: the best offset is the lexicographically-minimal rotation
\* of the input string, and among rotations that produce the same string
\* it has the smallest shift value.
Correctness ==
  /\ Terminated
  /\ \A j \in 0..(n - 1):
       /\ \A k \in 0..(n - 1):
            LET a == (best + k) % n
                b == (best + j) % n
                c == (j + k) % n
                d == (j + j) % n
                e == (j + c) % n
                f == (j + d) % n
            IN IF str[a + 1] = str[b + 1]
               THEN IF str[e + 1] = str[f + 1] THEN TRUE ELSE str[e + 1] <= str[f + 1]
               ELSE str[a + 1] <= str[b + 1]
       /\ (\A k \in 1..(n - 1): str[(best + k) % n + 1] = str[(best + 0) % n + 1])
          => best <= j

Termination == Terminated
====