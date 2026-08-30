---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* The lexicographically-least circular substring algorithm from Booth 1980     *)
(* runs in linear time using a failure function.  The character set is a         *)
(* finite subset of Nat, redefined below so the model stays finite.              *)

(* Replaces: the .cfg entry [ZSequences]Nat (a finite version of Nat from        *)
(* Naturals) with a declaration below.  'Nat' stays in scope from Naturals.      *)

CONSTANTS CharacterSet

Sentinel == 0 - 1

VARIABLES str, n, failFn, pmi, outer, bestOff, pc

vars == <<str, n, failFn, pmi, outer, bestOff, pc>>

TypeInvariant ==
  /\ str \in [0..(n - 1) -> CharacterSet]
  /\ n \in Nat
  /\ failFn \in [0..(n + n - 1) -> (Nat \cup {Sentinel})]
  /\ pmi \in (Nat \cup {Sentinel})
  /\ outer \in Nat
  /\ bestOff \in 0..(n - 1)
  /\ pc \in {"outerCheck", "lookup", "innerLoop", "updateBest", "failureFollow",
              "postCompare", "increment", "done"}

Init ==
  /\ \E s \in [1..(n + n - 1)] -> [i \in 0..(s - 1) |-> CHOOSE c \in CharacterSet : TRUE]
  /\ n = Len(s)
  /\ failFn = [i \in 0..(n + n - 1) |-> Sentinel]
  /\ pmi = Sentinel
  /\ outer = 1
  /\ bestOff = 0
  /\ pc = "outerCheck"

OuterCheck ==
  /\ pc = "outerCheck"
  /\ IF outer < (n + n) THEN pc' = "lookup" ELSE pc' = "done"
  /\ UNCHANGED <<str, n, failFn, pmi, outer, bestOff>>

Lookup ==
  /\ pc = "lookup"
  /\ failFn' = [failFn EXCEPT ![outer] = failFn[bestOff + outer]]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, n, pmi, outer, bestOff>>

InnerLoop ==
  /\ pc = "innerLoop"
  /\ IF str[outer % n] # str[(bestOff + outer) % n] /\ pmi # Sentinel
       THEN pc' = "innerLoop" ELSE pc' = "postCompare"
  /\ UNCHANGED <<str, n, failFn, pmi, outer, bestOff>>

UpdateBest ==
  /\ pc = "updateBest"
  /\ str[outer % n] < str[(bestOff + outer) % n]
  /\ bestOff' = outer % n
  /\ pc' = "failureFollow"
  /\ UNCHANGED <<str, n, failFn, pmi, outer>>

FailureFollow ==
  /\ pc = "failureFollow"
  /\ pmi' = failFn[pmi]
  /\ pc' = "innerLoop"
  /\ UNCHANGED <<str, n, failFn, outer, bestOff>>

PostCompare ==
  /\ pc = "postCompare"
  /\ IF str[outer % n] # str[(bestOff + outer) % n] /\ pmi = Sentinel
       THEN IF str[outer % n] < str[(bestOff + outer) % n]
               THEN bestOff' = outer % n
               ELSE bestOff' = bestOff
            /\ failFn' = [failFn EXCEPT ![bestOff + outer] = Sentinel]
            /\ pc' = "increment"
       ELSE IF str[outer % n] # str[(bestOff + outer) % n]
               THEN pc' = "failureFollow"
               ELSE pc' = "increment"
            /\ failFn' = [failFn EXCEPT ![bestOff + outer] = pmi + 1]
            /\ UNCHANGED <<str, n, pmi, outer, bestOff>>

Increment ==
  /\ pc = "increment"
  /\ outer' = outer + 1
  /\ pc' = "outerCheck"
  /\ UNCHANGED <<str, n, failFn, pmi, bestOff>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck \/ Lookup \/ InnerLoop \/ UpdateBest \/ FailureFollow
  \/ PostCompare \/ Increment \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(OuterCheck) /\ WF_vars(Lookup)
        /\ WF_vars(InnerLoop) /\ WF_vars(PostCompare) /\ WF_vars(Increment)

(* The best offset points to a rotation that is lexicographically minimal.      *)
Correctness ==
  /\ \A k \in 1..(n - 1) : \A i \in 0..(n - 1) :
        str[(bestOff + i) % n] = str[(bestOff + k + i) % n]
        => k = 0 \/ (\A i \in 0..(n - 1) : str[(i) % n] <= str[(k + i) % n])

Termination == <>(pc = "done")

====