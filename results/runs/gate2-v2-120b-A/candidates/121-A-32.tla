---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants (set by the .cfg file)
-----------------------------------------------------------------*)
CONSTANTS CharacterSet, Nat

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
Sentinel == -1

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES input, len, f, p, i, best, pc

(*-----------------------------------------------------------------
  Type definitions
-----------------------------------------------------------------*)
Chars == CharacterSet
String == Seq(Chars)

(*-----------------------------------------------------------------
  Type invariant (used also as a safety property)
-----------------------------------------------------------------*)
TypeOK ==
    /\ input \in String
    /\ len = Len(input)
    /\ f \in [0..2*len -> Nat \cup {Sentinel}]
    /\ p \in Nat \cup {Sentinel}
    /\ i \in Nat
    /\ 1 <= i <= 2*len + 1           \* +1 allows the terminating value
    /\ best \in 0..len-1
    /\ pc \in {"OuterCheck", "Lookup", "InnerCheck", "UpdateBest",
               "FollowFailure", "PostComp", "IncI", "Done"}

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
ModIdx(j) == j % len

CharAt(pos) == input[ModIdx(pos) + 1]   \* sequences are 1-indexed in TLA+

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ input \in String
    /\ len = Len(input)
    /\ f = [j \in 0..2*len |-> Sentinel]
    /\ p = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

(*-----------------------------------------------------------------
  Actions (one per labelled step)
-----------------------------------------------------------------*)
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i > 2*len
          THEN /\ pc' = "Done"
                /\ UNCHANGED <<input, len, f, p, i, best>>
          ELSE /\ pc' = "Lookup"
                /\ UNCHANGED <<input, len, f, p, i, best>>

Lookup ==
    /\ pc = "Lookup"
    /\ LET idx == i - best - 1 IN
       /\ p' = IF idx >= 0 /\ idx <= 2*len
                THEN f[idx]
                ELSE Sentinel
    /\ pc' = "InnerCheck"
    /\ UNCHANGED <<input, len, f, i, best>>

InnerCheck ==
    /\ pc = "InnerCheck"
    /\ IF p # Sentinel /\ CharAt(i) # CharAt(i - p - 1)
          THEN /\ pc' = "Lookup"
                /\ UNCHANGED <<input, len, f, p, i, best>>
          ELSE
               /\ IF CharAt(i) # CharAt(i - p - 1) /\ p = Sentinel
                     THEN /\ pc' = "PostComp"
                  ELSE
                     /\ pc' = IF CharAt(i) # CharAt(i - p - 1)
                               THEN "PostComp"
                               ELSE IF CharAt(i) < CharAt(i - p - 1)
                                      THEN "UpdateBest"
                                      ELSE "FollowFailure"
               /\ UNCHANGED <<input, len, f, p, i, best>>

UpdateBest ==
    /\ pc = "UpdateBest"
    /\ best' = ModIdx(i)
    /\ pc' = "FollowFailure"
    /\ UNCHANGED <<input, len, f, p, i>>

FollowFailure ==
    /\ pc = "FollowFailure"
    /\ LET idx == i - best - 1 IN
       /\ p' = IF idx >= 0 /\ idx <= 2*len
                THEN f[idx]
                ELSE Sentinel
    /\ pc' = "IncI"
    /\ UNCHANGED <<input, len, f, i, best>>

PostComp ==
    /\ pc = "PostComp"
    /\ IF CharAt(i) # CharAt(i - p - 1) /\ p = Sentinel
          THEN /\ IF CharAt(i) < CharAt(i - p - 1)
                    THEN best' = ModIdx(i)
                    ELSE UNCHANGED best
               /\ f' = [f EXCEPT ![i - best - 1] = Sentinel]
          ELSE /\ IF CharAt(i) = CharAt(i - p - 1)
                    THEN f' = [f EXCEPT ![i - best - 1] = p + 1]
                    ELSE f' = f
               /\ UNCHANGED best
    /\ pc' = "IncI"
    /\ UNCHANGED <<input, len, p, i>>

IncI ==
    /\ pc = "IncI"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<input, len, f, p, best>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<input, len, f, p, i, best, pc>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ OuterCheck
    \/ Lookup
    \/ InnerCheck
    \/ UpdateBest
    \/ FollowFailure
    \/ PostComp
    \/ IncI
    \/ Done

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<input, len, f, p, i, best, pc>>

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
TypeInvariant == TypeOK

(\* Correctness: best identifies a lexicographically minimal rotation *)
Correctness ==
    /\ TypeOK
    /\ \A shift \in 0..len-1 :
          LET rot(j) == input[(j + best) % len + 1] IN
          LET other(j) == input[(j + shift) % len + 1] IN
          ( \E k \in 1..len :
                /\ \A j \in 1..k-1 : rot(j) = other(j)
                /\ rot(k) < other(k) )
          \/ ( \A j \in 1..len : rot(j) = other(j) /\ best <= shift )

====