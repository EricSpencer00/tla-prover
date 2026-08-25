---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(***************************************************************************)
(*  Constants                                                             *)
(***************************************************************************)

CONSTANTS
    CharacterSet   \* finite subset of Nat, supplied by the .cfg file

ASSUME CharacterSet \subseteq Nat

(***************************************************************************)
(*  Sentinel value for undefined entries in the failure function           *)
(***************************************************************************)

Sentinel == -1

(***************************************************************************)
(*  Variables                                                             *)
(***************************************************************************)

VARIABLES
    s,           \* the input string: function 0..len-1 -> CharacterSet
    len,         \* length of the string
    f,           \* failure function array indexed 0..2*len
    pIdx,        \* pattern‑match index (may be Sentinel)
    i,           \* outer loop counter, runs from 1 up to 2*len
    best,        \* current best rotation offset
    pc           \* program counter (labels of the algorithm)

vars == << s, len, f, pIdx, i, best, pc >>

(***************************************************************************)
(*  Helper definitions                                                    *)
(***************************************************************************)

Idx(j) == (j) % len                     \* modulo indexing (0‑based)

Rot(off) == [k \in 0..len-1 |-> s[Idx(off + k)]]

LexLe(rot1, rot2) ==
    \A k \in 0..len-1 :
        ( \A j \in 0..k-1 : rot1[j] = rot2[j] ) => rot1[k] <= rot2[k]

MinRot ==
    CHOOSE off \in 0..len-1 :
        \A shift \in 0..len-1 : LexLe(Rot(off), Rot(shift))

(***************************************************************************)
(*  Initial state                                                         *)
(***************************************************************************)

Init ==
    /\ len \in Nat
    /\ s \in [0..len-1 -> CharacterSet]
    /\ f = [j \in 0..2*len |-> Sentinel]
    /\ pIdx = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(***************************************************************************)
(*  Actions                                                               *)
(***************************************************************************)

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2*len
       THEN /\ pc' = "Lookup"
            /\ UNCHANGED << s, len, f, pIdx, i, best >>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << s, len, f, pIdx, i, best >>

Lookup ==
    /\ pc = "Lookup"
    /\ idx == Idx(i + best)
    /\ pIdx' = f[idx]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED << s, len, f, i, best >>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ a == s[Idx(i)]
    /\ b == s[Idx(best + (pIdx + 1))]
    /\ IF pIdx = Sentinel
          THEN /\ pc' = "PostComp"
               /\ UNCHANGED << s, len, f, i, best, pIdx >>
       ELSE IF a = b
          THEN /\ pIdx' = pIdx + 1
               /\ pc' = "InnerLoop"
               /\ UNCHANGED << s, len, f, i, best >>
          ELSE /\ pc' = "Update"
               /\ UNCHANGED << s, len, f, i, best, pIdx >>

Update ==
    /\ pc = "Update"
    /\ a == s[Idx(i)]
    /\ b == s[Idx(best + (pIdx + 1))]
    /\ IF a < b
          THEN best' = Idx(i)
          ELSE best' = best
    /\ pc' = "FollowFail"
    /\ UNCHANGED << s, len, f, i, pIdx >>

FollowFail ==
    /\ pc = "FollowFail"
    /\ idx == Idx(i + best)
    /\ pIdx' = f[idx]
    /\ pc' = "PostComp"
    /\ UNCHANGED << s, len, f, i, best >>

PostComp ==
    /\ pc = "PostComp"
    /\ a == s[Idx(i)]
    /\ b == s[Idx(best + (pIdx + 1))]
    /\ IF a # b /\ pIdx = Sentinel
          THEN /\ IF a < b
                    THEN best' = Idx(i)
                    ELSE best' = best
               /\ f' = [f EXCEPT ![Idx(i + best)] = Sentinel]
          ELSE /\ f' = f
    /\ pc' = "Inc"
    /\ UNCHANGED << s, len, i, pIdx >>

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED << s, len, f, pIdx, best >>

DoneStutter ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ Update
    \/ FollowFail
    \/ PostComp
    \/ Inc
    \/ DoneStutter

(***************************************************************************)
(*  Specification                                                         *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*  Type invariant                                                        *)
(***************************************************************************)

TypeInvariant ==
    /\ s \in [0..len-1 -> CharacterSet]
    /\ len \in Nat
    /\ f \in [0..2*len -> Nat \cup {Sentinel}]
    /\ pIdx \in Nat \cup {Sentinel}
    /\ i \in Nat
    /\ best \in 0..len-1
    /\ pc \in {"OuterCheck","Lookup","InnerLoop","Update",
               "FollowFail","PostComp","Inc","Done"}

(***************************************************************************)
(*  Correctness property                                                  *)
(***************************************************************************)

Correctness ==
    /\ pc = "Done"
    /\ \A shift \in 0..len-1 :
          LexLe(Rot(best), Rot(shift))
          /\ ( Rot(best) = Rot(shift) => best <= shift )

(***************************************************************************)
(*  End of module                                                         *)
(***************************************************************************)

====