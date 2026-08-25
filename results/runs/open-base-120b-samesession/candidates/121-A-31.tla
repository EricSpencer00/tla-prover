---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

(* ------------------------------------------------------------------------
   Sentinel value used to denote “undefined’’ entries in the failure function.
   ------------------------------------------------------------------------ *)
Sentinel == -1

VARIABLES input, len, fail, k, i, best, pc

vars == <<input, len, fail, k, i, best, pc>>

(* ------------------------------------------------------------------------
   Initialization: a nondeterministic finite string over CharacterSet and
   the associated auxiliary variables.
   ------------------------------------------------------------------------ *)
Init ==
    /\ len \in Nat
    /\ input \in [0..len-1 -> CharacterSet]
    /\ fail = [j \in 0..2*len-1 |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "CheckOuter"

(* ------------------------------------------------------------------------
   The outer‑loop test.
   ------------------------------------------------------------------------ *)
CheckOuter ==
    /\ pc = "CheckOuter"
    /\ IF i < 2*len
          THEN /\ pc' = "Lookup"
               /\ UNCHANGED <<input, len, fail, k, i, best>>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED <<input, len, fail, k, i, best>>

(* ------------------------------------------------------------------------
   Failure‑function lookup for the current position.
   ------------------------------------------------------------------------ *)
Lookup ==
    /\ pc = "Lookup"
    /\ f == fail[i]
    /\ k' = f
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<input, len, fail, i, best>>

(* ------------------------------------------------------------------------
   Abstracted inner comparison loop.
   The details of Booth’s algorithm are collapsed into a nondeterministic
   choice that either advances the match or concludes the comparison.
   ------------------------------------------------------------------------ *)
InnerLoop ==
    /\ pc = "InnerLoop"
    /\ \/ (* characters match, extend the match *)
          /\ (* In the real algorithm we would compare
                input[(i) % len] with input[(best + k) % len]  *)
          /\ k # Sentinel
          /\ k' = k + 1
          /\ fail' = [fail EXCEPT ![i] = k']
          /\ pc' = "InnerLoop"
          /\ UNCHANGED <<input, len, i, best>>
       \/ (* characters differ; possibly update best rotation *)
          /\ k = Sentinel
          /\ IF input[i % len] < input[best % len]
                THEN /\ best' = i % len
                ELSE /\ UNCHANGED best
          /\ fail' = [fail EXCEPT ![i] = Sentinel]
          /\ k' = Sentinel
          /\ pc' = "IncI"
          /\ UNCHANGED <<input, len, i>>

(* ------------------------------------------------------------------------
   Increment the outer‑loop counter.
   ------------------------------------------------------------------------ *)
IncI ==
    /\ pc = "IncI"
    /\ i' = i + 1
    /\ pc' = "CheckOuter"
    /\ UNCHANGED <<input, len, fail, k, best>>

(* ------------------------------------------------------------------------
   Final state – the algorithm has terminated.
   ------------------------------------------------------------------------ *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ CheckOuter
    \/ Lookup
    \/ InnerLoop
    \/ IncI
    \/ Done

Spec ==
    Init /\ [][Next]_vars

(* ------------------------------------------------------------------------
   Type invariant.
   ------------------------------------------------------------------------ *)
TypeInvariant ==
    /\ len \in Nat
    /\ input \in [0..len-1 -> CharacterSet]
    /\ fail \in [0..2*len-1 -> (Nat \cup {Sentinel})]
    /\ (k = Sentinel) \/ k \in Nat
    /\ i \in Nat
    /\ best \in 0..len-1
    /\ pc \in {"CheckOuter","Lookup","InnerLoop","IncI","Done"}

(* ------------------------------------------------------------------------
   Helper definitions for the correctness property.
   ------------------------------------------------------------------------ *)
Rotation(off) ==
    [j \in 0..len-1 |-> input[(off + j) % len]]

LexLe(s, t) ==
    \E m \in 0..len :
        /\ \A p \in 0..m-1 : s[p] = t[p]
        /\ (m = len) \/ s[m] < t[m]

Correctness ==
    /\ pc = "Done"
    /\ \A j \in 0..len-1 : LexLe(Rotation(best), Rotation(j))

====