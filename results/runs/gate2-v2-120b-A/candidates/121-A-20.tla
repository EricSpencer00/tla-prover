---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(*************************************************************************)
(*  Constants                                                            *)
(*************************************************************************)
CONSTANTS CharacterSet, Nat

(*************************************************************************)
(*  Sentinel value for "undefined" entries in the failure function        *)
(*************************************************************************)
Sentinel == -1

(*************************************************************************)
(*  State variables                                                      *)
(*************************************************************************)
VARIABLES
    InputStr,          \* Sequence of characters (zero-indexed)
    Len,               \* Length of InputStr
    Fail,              \* Failure function array, indexed 0..2*Len-1
    P,                 \* Pattern-match index (or Sentinel)
    I,                 \* Outer loop counter, runs from 1 to 2*Len
    Best,              \* Best rotation offset found so far
    pc                 \* Program counter (label of the current step)

(*************************************************************************)
(*  Helper definitions                                                  *)
(*************************************************************************)
Idx(i) == i % Len                     \* Circular indexing into InputStr
CharAt(i) == InputStr[Idx(i)]         \* Character at position i (mod Len)

\* The domain of the failure function during execution
FailDomain == 0 .. (2 * Len - 1)

(*************************************************************************)
(*  Initial state (init)                                                *)
(*************************************************************************)
Init ==
    /\ Len \in Nat
    /\ Len >= 1
    /\ InputStr = [i \in 0..Len-1 |-> CHOOSE x \in CharacterSet : TRUE]
    /\ Fail = [j \in FailDomain |-> Sentinel]
    /\ P = Sentinel
    /\ I = 1
    /\ Best = 0
    /\ pc = "OuterCheck"

(*************************************************************************)
(*  Actions                                                             *)
(*************************************************************************)

OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF I >= 2 * Len
          THEN /\ pc' = "Done"
               /\ UNCHANGED <<InputStr, Len, Fail, P, I, Best>>
          ELSE /\ pc' = "Lookup"
               /\ UNCHANGED <<InputStr, Len, Fail, P, I, Best>>

Lookup ==
    /\ pc = "Lookup"
    /\ let idx == (Best + I) % Len in
       /\ IF Fail[idx] # Sentinel
             THEN /\ P' = Fail[idx]
                  /\ pc' = "InnerLoop"
             ELSE /\ P' = Sentinel
                  /\ pc' = "InnerLoop"
    /\ UNCHANGED <<InputStr, Len, Fail, I, Best>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF (P # Sentinel) /\ CharAt(I) = CharAt(Best + P + 1)
          THEN /\ pc' = "InnerLoop"
               /\ P' = P + 1
               /\ UNCHANGED <<InputStr, Len, Fail, I, Best>>
          ELSE /\ pc' = "AfterInner"
               /\ UNCHANGED <<InputStr, Len, Fail, I, Best, P>>

AfterInner ==
    /\ pc = "AfterInner"
    /\ IF P = Sentinel /\ CharAt(I) < CharAt(Best + 1)
          THEN /\ Best' = I
               /\ pc' = "PostCompare"
          ELSE /\ Best' = Best
               /\ pc' = "PostCompare"
    /\ UNCHANGED <<InputStr, Len, Fail, I, P>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ IF CharAt(I) # CharAt(Best + 1) /\ P = Sentinel
          THEN /\ FAIL_SET = [j \in FailDomain |-> IF j = (Best + I) % Len
                                            THEN Sentinel
                                            ELSE Fail[j]]
               /\ Fail' = Fail_SET
               /\ P' = Sentinel
               /\ pc' = "Inc"
          ELSE /\ Fail' = [Fail EXCEPT ![(Best + I) % Len] = P + 1]
               /\ pc' = "Inc"
    /\ UNCHANGED <<InputStr, Len, I, Best>>

Inc ==
    /\ pc = "Inc"
    /\ I' = I + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<InputStr, Len, Fail, P, Best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<InputStr, Len, Fail, P, I, Best, pc>>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<InputStr, Len, Fail, P, I, Best, pc>>

(*************************************************************************)
(*  Next-state relation                                                  *)
(*************************************************************************)
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ AfterInner
    \/ PostCompare
    \/ Inc
    \/ Done
    \/ Stutter

(*************************************************************************)
(*  Specification (temporal formula)                                      *)
(*************************************************************************)
Spec == Init /\ [][Next]_<<InputStr, Len, Fail, P, I, Best, pc>>

(*************************************************************************)
(*  Type invariant                                                       *)
(*************************************************************************)
TypeInvariant ==
    /\ Len \in Nat
    /\ Len >= 1
    /\ InputStr \in [0..Len-1 -> CharacterSet]
    /\ Fail \in [FailDomain -> (Sentinel \cup Nat)]
    /\ P \in Sentinel \cup Nat
    /\ I \in 1..2*Len
    /\ Best \in 0..Len-1
    /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "AfterInner",
               "PostCompare", "Inc", "Done"}

(*************************************************************************)
(*  Correctness invariant: Best points to the lexicographically minimal *)
(*  rotation of InputStr.                                                *)
(*************************************************************************)
IsRotation(s, off) ==
    /\ Len = Len(s)
    /\ [i \in 0..Len-1 |-> s[(i + off) % Len]]

Correctness ==
    \A off \in 0..Len-1 :
        IsRotation(InputStr, Best) <= IsRotation(InputStr, off)

(*************************************************************************)
(*  Theorems (optional, kept for completeness)                           *)
(*************************************************************************)
THEOREM SpecImpliesTypeInv == Spec => []TypeInvariant

THEOREM SpecImpliesCorrectness == Spec => []Correctness

=============================================================================