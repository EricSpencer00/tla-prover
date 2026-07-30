---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    CharacterSet,
    Nat

\* Zero-indexed strings over a finite character set; the corpus is all such
\* strings up to the model-checking bound on length.
Corpus == [n \in Nat |-> Seq(CharacterSet)]

VARIABLES
    string,
    n,
    fail,
    pat,
    i,
    best,
    pc

vars == <<string, n, fail, pat, i, best, pc>>

\* Sentinel value meaning "failure function undefined" (always distinct from
\* any valid index).
Undefined == 0

Steps == {"OuterCheck", "LookupFail", "InnerLoop", "UpdateBest", "FollowFail",
          "PostCmp", "Advance"}

TypeOK ==
    /\ string \in Corpus
    /\ n \in Nat
    /\ fail \in [0..2 * n -> 0..n]
    /\ pat \in 0..n
    /\ i \in 0..(2 * n - 1)
    /\ best \in 0..(n - 1)
    /\ pc \in Steps

Init ==
    /\ \E s \in Corpus : string = s
    /\ n = Len(string)
    /\ fail = [k \in 0..(2 * n) |-> Undefined]
    /\ pat = Undefined
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

OuterCheck ==
    /\ i < 2 * n
    /\ pc' = "LookupFail"
    /\ UNCHANGED <<string, n, fail, pat, i, best>>

LookupFail ==
    /\ pc' = "InnerLoop"
    /\ pat' = fail[(i - best) % n]
    /\ UNCHANGED <<string, n, fail, i, best>>

InnerLoop ==
    /\ pc' = IF string[(i % n)] # string[((i + pat) % n)]
                 /\ pat = Undefined
                 THEN "PostCmp" ELSE "UpdateBest"
    /\ UNCHANGED <<string, n, fail, i, best>>

UpdateBest ==
    /\ \A k \in 0..(n - 1) : string[(i + k) % n] >= string[(best + k) % n]
    /\ best' = i % n
    /\ pc' = "FollowFail"
    /\ UNCHANGED <<string, n, fail, pat, i>>

FollowFail ==
    /\ pat' = fail[pat]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<string, n, fail, i, best>>

PostCmp ==
    /\ IF \A k \in 0..(n - 1) : string[(i + k) % n] >= string[(best + k) % n]
         THEN best' = best
         ELSE best' = i % n
    /\ fail' = [fail EXCEPT ![((i - best) % n)] = IF pat = Undefined
                                                    THEN Undefined
                                                    ELSE pat + 1]
    /\ pc' = "Advance"
    /\ UNCHANGED <<string, n, pat, i>>

Advance ==
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<string, n, fail, pat, best>>

Terminate ==
    /\ ~(\E s \in Steps : pc = s)
    /\ UNCHANGED vars

Stall ==
    /\ \A s \in Steps : pc = s
    /\ UNCHANGED vars

Next == OuterCheck \/ LookupFail \/ InnerLoop \/ UpdateBest \/ FollowFail
        \/ PostCmp \/ Advance \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Advance)

Correctness ==
    /\ n > 0
    /\ \A k \in 0..(n - 1) :
         /\ string[(best + k) % n] >= string[(best + 0) % n]
         /\ \A j \in 1..(n - 1) : string[(best + j) % n] >= string[(best + 0) % n]
    /\ \A j \in 0..(n - 1) :
         string[(best + j) % n] <= string[(j + 0) % n]

Termination == <>(\A s \in Steps : pc = s)

====