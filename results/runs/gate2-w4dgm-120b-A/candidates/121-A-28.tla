---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* Override the usual Naturals domain with a finite set so the model stays
\* small, while keeping the full arithmetic operators from Naturals.
Nat == CharacterSet

Zero == 0
Sentinel == Cardinality(CharacterSet)

VARIABLES str, n, failure, pmatch, i, offset, pc

vars == <<str, n, failure, pmatch, i, offset, pc>>

TypeInvariant ==
    /\ str \in [1..Cardinality(CharacterSet) -> CharacterSet]
    /\ n = Len(str)
    /\ failure \in [0..2 * n -> 0..Cardinality(CharacterSet)]
    /\ pmatch \in 0..Cardinality(CharacterSet)
    /\ i \in 1..(2 * n + 1)
    /\ offset \in 0..(n - 1)
    /\ pc \in {"outer", "lookup", "compare", "update", "follow", "post", "done"}

Init ==
    /\ \E s \in [1..Cardinality(CharacterSet) -> CharacterSet] : str = s
    /\ n = Len(str)
    /\ failure = [k \in 0..(2 * CardIdx(str)) |-> Sentinel]
    /\ pmatch = Sentinel
    /\ i = 1
    /\ offset = 0
    /\ pc = "outer"

OuterLoop ==
    /\ pc = "outer"
    /\ IF i < 2 * n
       THEN pc' = "lookup"
       ELSE pc' = "done"
    /\ UNCHANGED <<str, n, failure, pmatch, i, offset>>

Lookup ==
    /\ pc = "lookup"
    /\ failure' = [failure EXCEPT ![i - offset] = Sentinel]
    /\ pmatch' = Sentinel
    /\ pc' = "compare"
    /\ UNCHANGED <<str, n, i, offset>>

Compare ==
    /\ pc = "compare"
    /\ LET a == str[(i % n) + 1] b == str[(i + offset) % n + 1] IN
         /\ (a # b /\ pmatch # Sentinel) => pc' = "follow"
         /\ (a # b /\ pmatch = Sentinel) => pc' = "post"
         /\ (a = b) => pc' = "compare"
    /\ UNCHANGED <<str, n, failure, pmatch, i, offset>>

Update ==
    /\ pc = "update"
    /\ LET a == str[(i % n) + 1] b == str[(i + offset) % n + 1] IN
         /\ IF a < b THEN offset' = i ELSE offset' = offset
    /\ UNCHANGED <<str, n, failure, pmatch, i, pc>>

Follow ==
    /\ pc = "follow"
    /\ pmatch' = failure[i - offset]
    /\ UNCHANGED <<str, n, failure, i, offset, pc>>

Post ==
    /\ pc = "post"
    /\ LET a == str[(i % n) + 1] b == str[(i + offset) % n + 1] IN
         /\ IF a # b /\ pmatch = Sentinel /\ a < b THEN offset' = i ELSE offset' = offset
    /\ failure' = [failure EXCEPT ![i - offset] =
                     IF a = b THEN failure[i - offset] ELSE
                        IF pmatch = Sentinel THEN Sentinel ELSE pmatch + 1]
    /\ pc' = "advance"
    /\ UNCHANGED <<str, n, pmatch, i>>

Advance ==
    /\ pc = "advance"
    /\ i' = i + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<str, n, failure, pmatch, offset>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ OuterLoop \/ Lookup \/ Compare \/ Update
    \/ Follow \/ Post \/ Advance \/ Done

Spec == Init /\ [][Next]_vars
        /\ WF_vars(OuterLoop) /\ WF_vars(Lookup) /\ WF_vars(Compare)
        /\ WF_vars(Follow) /\ WF_vars(Post) /\ WF_vars(Advance)

\* On termination, the best rotation is lexicographically minimal (and the
\* smallest such shift, when equality ties) among all rotations of the string.
RotationalOrder ==
    /\ Len(Rotate(i)) = n
    /\ \A j \in 0..(n - 1) : Rotate(i) <= Rotate(j)
    /\ \A k \in 0..(n - 1) : (Rotate(i) = Rotate(k) => i <= k)
    /\ i = offset

Rotate(i) == [k \in 1..n |-> str[((i + k - 1) % n) + 1]]

Correctness == (pc = "done") => RotationalOrder

Termination == <>(pc = "done")

====