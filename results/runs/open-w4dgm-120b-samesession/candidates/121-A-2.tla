---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

(* Zero-indexed character sequence (the "corpus" of all sequences of any   *)
(* length) is defined from the finite set CharacterSet.                    *)

Corpus == { s \in Seq(CharacterSet) : \A i \in DOMAIN s : s[i] \in CharacterSet }

(* The failure function array is indexed from 0 up to twice the string      *)
(* length, and maps to a valid index or the sentinel "undefined".          *)

VARIABLES string, length, fail, pIdx, k, best, pc

vars == << string, length, fail, pIdx, k, best, pc >>

Sentinel == 4294967295

TypeInvariant ==
    /\ string \in Corpus
    /\ length = Len(string)
    /\ fail \in [0 .. 2 * length -> 0 .. 2 * length \cup {Sentinel}]
    /\ pIdx \in 0 .. 2 * length \cup {Sentinel}
    /\ k \in 0 .. 2 * length
    /\ best \in 0 .. (IF length = 0 THEN 0 ELSE length - 1)
    /\ pc \in {"OuterCheck", "Lookup", "InnerComp", "UpdateBest", "FollowFail",
               "PostCompare", "Done"}

Init ==
    /\ \E s \in Corpus : string = s
    /\ length = Len(string)
    /\ fail = [i \in 0 .. 2 * length |-> Sentinel]
    /\ pIdx = Sentinel
    /\ k = 1
    /\ best = 0
    /\ pc = "OuterCheck"

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ pc' = IF k >= 2 * length THEN "Done" ELSE "Lookup"
    /\ UNCHANGED << string, length, fail, pIdx, k, best >>

Lookup ==
    /\ pc = "Lookup"
    /\ pIdx' = fail[k - 1]
    /\ pc' = "InnerComp"
    /\ UNCHANGED << string, length, fail, k, best >>

InnerComp ==
    /\ pc = "InnerComp"
    /\ LET c1 == string[((k - 1) % length) + 1]
           c2 == string[((best + k - 1) % length) + 1] IN
       /\ IF c1 # c2 /\ pIdx # Sentinel
          THEN pc' = "InnerComp"
          ELSE pc' = "PostCompare"
    /\ UNCHANGED << string, length, fail, pIdx, k, best >>

UpdateBest ==
    /\ pc = "UpdateBest"
    /\ LET c1 == string[((k - 1) % length) + 1]
           c2 == string[((best + k - 1) % length) + 1] IN
       /\ IF c1 < c2 THEN best' = (best + k) % length ELSE best' = best
    /\ pc' = "FollowFail"
    /\ UNCHANGED << string, length, fail, pIdx, k >>

FollowFail ==
    /\ pc = "FollowFail"
    /\ pIdx' = fail[pIdx]
    /\ pc' = "InnerComp"
    /\ UNCHANGED << string, length, fail, k, best >>

PostCompare ==
    /\ pc = "PostCompare"
    /\ LET c1 == string[((k - 1) % length) + 1]
           c2 == string[((best + k - 1) % length) + 1] IN
       /\ IF /\ c1 # c2
             /\ pIdx = Sentinel
             /\ c1 < c2
          THEN best' = (best + k) % length
          ELSE best' = best
       /\ fail' = [fail EXCEPT ![k - 1] =
                      IF c1 = c2 THEN Sentinel ELSE IF pIdx = Sentinel THEN 0 ELSE pIdx + 1]
    /\ pc' = "OuterCheck"
    /\ k' = k + 1
    /\ UNCHANGED << string, length, pIdx >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Stall ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck \/ Lookup \/ InnerComp \/ UpdateBest \/ FollowFail
    \/ PostCompare \/ Done \/ Stall

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(OuterCheck) /\ WF_vars(Lookup) /\ WF_vars(InnerComp)
    /\ WF_vars(UpdateBest) /\ WF_vars(FollowFail) /\ WF_vars(PostCompare)

(* Upon termination, the rotation at "best" is lexicographically minimal: *)
(* no other rotation is strictly smaller, and rotations that are equal    *)
(* compare on shift value alone so the smallest shift survives.           *)
Correctness ==
    /\ pc = "Done"
    /\ \A i \in 0 .. length - 1 :
        /\ LET rBest == CHOOSE t \in 0 .. length - 1 :
                        \A j \in 0 .. length - 1 :
                            (t # j => Rotate(string, t) %< Rotate(string, j))
                            /\ (t = j => TRUE)
             rAlt == Rotate(string, i) IN
           /\ rBest %<= rAlt
           /\ (rBest = rAlt => best <= i)

Terminate == <>(pc = "Done")

====