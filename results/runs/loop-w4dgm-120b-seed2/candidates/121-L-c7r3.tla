---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS CharacterSet

VARIABLES string, length, fail, failure, k, best, pc

vars == <<string, length, fail, failure, k, best, pc>>
MaxLen == 2
Sentinel == MaxLen

\* CharacterSet replaces the built-in Nat entirely, so it must be declared
\* here (in a finite, model-checkable form) rather than referenced as a
\* separate module name.
CharacterSet == Nat

TypeInvariant ==
    /\ string \in [0 .. MaxLen -> CharacterSet]
    /\ length = Len(string)
    /\ fail \in [0 .. 2 * MaxLen -> 0 .. MaxLen]
    /\ failure \in 0 .. MaxLen
    /\ k \in 0 .. 2 * MaxLen
    /\ best \in 0 .. MaxLen
    /\ pc \in {"outer", "lookup", "inner", "branchless", "follow", "post", "done"}

Init ==
    /\ \E s \in [0 .. MaxLen -> CharacterSet] : string = s
    /\ length = Len(string)
    /\ fail = [i \in 0 .. 2 * MaxLen |-> Sentinel]
    /\ failure = Sentinel
    /\ k = 1
    /\ best = 0
    /\ pc = "outer"

Outer ==
    /\ pc = "outer"
    /\ k < 2 * length
    /\ pc' = "lookup"
    /\ UNCHANGED <<string, length, fail, failure, k, best>>

Lookup ==
    /\ pc = "lookup"
    /\ fail' = [fail EXCEPT ![k - 1] = fail[k - 1]]
    /\ failure' = fail[k - 1]
    /\ pc' = "inner"
    /\ UNCHANGED <<string, length, k, best>>

Inner ==
    /\ pc = "inner"
    /\ string[k % length] /= string[(best + k) % length]
    /\ failure # Sentinel
    /\ pc' = "branchless"
    /\ UNCHANGED <<string, length, fail, failure, k, best>>

Branchless ==
    /\ pc = "branchless"
    /\ string[k % length] < string[(best + k) % length]
    /\ best' = k
    /\ pc' = "follow"
    /\ UNCHANGED <<string, length, fail, failure, k>>

Follow ==
    /\ pc = "follow"
    /\ failure' = fail[k - 1]
    /\ pc' = "post"
    /\ UNCHANGED <<string, length, fail, k, best>>

Post ==
    /\ pc = "post"
    /\ \/ (string[k % length] /= string[(best + k) % length] /\ failure = Sentinel /\ (string[k % length] < string[(best + k) % length] /\ best' = k))
       \/ (failure # Sentinel /\ fail' = [fail EXCEPT ![k] = failure])
    /\ k' = k + 1
    /\ pc' = "outer"
    /\ UNCHANGED <<string, length, failure>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Outer \/ Lookup \/ Inner \/ Branchless \/ Follow \/ Post \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Outer) /\ WF_vars(Lookup) /\ WF_vars(Branchless) /\ WF_vars(Post)

\* The recorded rotation must be lexicographically minimal and, among ties,
\* the earliest such rotation.
Correctness ==
    /\ \A i \in 0 .. length - 1 : string[(best + i) % length] <= string[i]
    /\ \A i \in 0 .. length - 1 :
         (string[(best + i) % length] = string[i]) => (i >= best \/ string[(best + i) % length] < string[i])

Termination == <>(pc = "done")

====