---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet

\* The role-named operators below are redefined in the .cfg to hide the
\* standard Naturals.Nat (a standard-infinite set) and replace it with a
\* checkable finite version; they must remain declared here as operators.
ZSequences == CharacterSet

VARIABLES str, n, fail, pat, i, best, pc

vars == <<str, n, fail, pat, i, best, pc>>

Sentinel == 0
MaxLen == 2

Corpora == UNION { [1 .. k -> ZSequences] : k \in 1..MaxLen }
NextIdx(x) == IF x < 2 * n THEN x + 1 ELSE x

TypeInvariant ==
  /\ str \in Corpora
  /\ n = Len(str)
  /\ fail \in [0 .. 2 * n -> 0 .. 2 * n]
  /\ pat \in 0 .. 2 * n
  /\ i \in 1 .. 2 * n + 1
  /\ best \in 0 .. MaxLen - 1
  /\ pc \in {"oCheck", "lookup", "innerLoop", "updateBest", "followFail", "postCmp", "inc"}

Init ==
  /\ \E s \in Corpora : str' = s
  /\ n' = Len(str)
  /\ fail' = [k \in 0 .. 2 * MaxLen |-> Sentinel]
  /\ pat' = Sentinel
  /\ i' = 1
  /\ best' = 0
  /\ pc' = "oCheck"

OCheck ==
  /\ pc = "oCheck"
  /\ IF i < 2 * n THEN pc' = "lookup" ELSE pc' = "stalled"
  /\ UNCHANGED <<str, n, fail, pat, i, best>>

Lookup ==
  /\ pc = "lookup"
  /\ pat' = fail[best + i - 1]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, n, fail, i, best>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ LET cur == str[(i - 1) % n + 1]
         cand == str[(best + i - 1) % n + 1] IN
       IF cur = cand THEN pc' = "postCmp"
       ELSE IF pat = Sentinel THEN pc' = "postCmp"
       ELSE pc' = "innerLoop"
  /\ UNCHANGED <<str, n, fail, pat, i, best>>

UpdateBest ==
  /\ pc = "innerLoop"
  /\ LET cur == str[(i - 1) % n + 1]
         cand == str[(best + i - 1) % n + 1] IN
       IF cur < cand THEN best' = i - 1
       ELSE best' = best
  /\ pc' = "followFail"
  /\ UNCHANGED <<str, n, fail, pat, i>>

FollowFail ==
  /\ pc = "followFail"
  /\ pat' = fail[pat]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, n, fail, i, best>>

PostCmp ==
  /\ pc = "postCmp"
  /\ LET cur == str[(i - 1) % n + 1]
         cand == str[(best + i - 1) % n + 1] IN
       /\ IF cur # cand /\ pat = Sentinel /\ cur < cand
          THEN best' = i - 1
          ELSE best' = best
       /\ fail' = [fail EXCEPT ![best + i - 1] =
                     IF cur # cand /\ pat = Sentinel THEN Sentinel ELSE pat + 1]
  /\ pc' = "inc"
  /\ UNCHANGED <<str, n, pat, i>>

Inc ==
  /\ pc = "inc"
  /\ i' = NextIdx(i)
  /\ pc' = "oCheck"
  /\ UNCHANGED <<str, n, fail, pat, best>>

Stalled ==
  /\ pc = "stalled"
  /\ UNCHANGED vars

Next == OCheck \/ Lookup \/ InnerLoop \/ UpdateBest \/ FollowFail \/ PostCmp \/ Inc \/ Stalled

Spec == Init /\ [][Next]_vars /\ WF_vars(OCheck) /\ WF_vars(Inc)

\* A rotation starting at offset o is the string viewed through modulo
\* indexing, and the offset count wraps at MaxLen. Rotate uses that wrap.
Rotate(o) ==
  LAMBDA k \in 1 .. n : str[((o + k - 2) % n) + 1]

AllRotationsLessOrEqual ==
  \A o \in 0 .. MaxLen - 1 :
    /\ Rotate(best) <= Rotate(o)
    /\ (Rotate(best) = Rotate(o) => best <= o)

Correctness == pc = "stalled" => AllRotationsLessOrEqual

Termination == <>(pc = "stalled")

====