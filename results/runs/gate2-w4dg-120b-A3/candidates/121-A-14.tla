---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences, ZSequences

CONSTANTS CharacterSet

VARIABLES str, n, fail, kmp, i, bestShift, pc
vars == <<str, n, fail, kmp, i, bestShift, pc>>

Zero == 0
Sentinel == 0
Strings == {s \in Seq(CharacterSet) : Len(s) >= 1 /\ Len(s) <= 2}
Rot(s, k) == << s[k + 1 .. Len(s)], s[1 .. k] >>

TypeInvariant ==
  /\ str \in Strings
  /\ n = Len(str)
  /\ fail \in [0 .. 2 * n -> 0 .. 2 * n]
  /\ kmp \in 0 .. 2 * n
  /\ i \in 1 .. 2 * n
  /\ bestShift \in 0 .. (n - 1)
  /\ pc \in {"outer", "lookup", "inner", "fallback", "post", "done"}

Init ==
  /\ str \in Strings
  /\ n = Len(str)
  /\ fail = [p \in 0 .. 2 * n |-> Sentinel]
  /\ kmp = Sentinel
  /\ i = 1
  /\ bestShift = 0
  /\ pc = "outer"

\* Outer loop: iterate over the doubled string (mod n for wrap-around).
OuterLoop ==
  /\ pc = "outer"
  /\ \E active \in BOOLEAN:
       /\ i < 2 * n => /\ pc' = "lookup"
                      /\ UNCHANGED <<str, n, fail, kmp, i, bestShift>>
       /\ i >= 2 * n => /\ pc' = "done"
                         /\ UNCHANGED <<str, n, fail, kmp, i, bestShift>>
       /\ (i < 2 * n) <=> active
       /\ UNCHANGED kmp

Lookup ==
  /\ pc = "lookup"
  /\ kmp' = fail[(i - 1) % n + bestShift]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, fail, i, bestShift>>

ActiveComp ==
  /\ str[i % n + 1] # str[(kmp + 1) % n + 1]
  /\ kmp # Sentinel

\* Follow the failure function chain during the inner comparison loop.
InnerLoop ==
  /\ pc = "inner"
  /\ \/ /\ ActiveComp
        /\ pc' = "fallback"
        /\ UNCHANGED <<str, n, fail, kmp, i, bestShift>>
     \/ /\ ~ActiveComp
        /\ pc' = "post"
        /\ UNCHANGED <<str, n, fail, kmp, i, bestShift>>

\* A genuine update: the current character is smaller, so shift the best rotation.
Fallback ==
  /\ pc = "fallback"
  /\ str[i % n + 1] < str[bestShift + 1]
  /\ bestShift' = (i - 1) % n
  /\ kmp' = fail[kmp]
  /\ pc' = "inner"
  /\ UNCHANGED <<str, n, fail, i>>

PostComp ==
  /\ pc = "post"
  /\ IF ~ActiveComp /\ kmp = Sentinel /\ str[i % n + 1] < str[bestShift + 1]
       THEN bestShift' = (i - 1) % n
       ELSE bestShift' = bestShift
  /\ fail' = [fail EXCEPT ![(i - 1) % n + bestShift] =
                 IF ~ActiveComp /\ kmp = Sentinel THEN Sentinel ELSE kmp + 1]
  /\ kmp' = Sentinel
  /\ pc' = "outer"
  /\ i' = i + 1
  /\ UNCHANGED str

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterLoop \/ Lookup \/ InnerLoop \/ Fallback \/ PostComp \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Lookup) /\ WF_vars(InnerLoop)
             /\ WF_vars(Fallback) /\ WF_vars(PostComp)

Correctness ==
  /\ \A k \in 0 .. (n - 1):
       Rot(str, bestShift) =< Rot(str, k)
  /\ \A k \in 0 .. (n - 1):
       Rot(str, bestShift) = Rot(str, k) => bestShift <= k

Termination == <>(pc = "done")
====