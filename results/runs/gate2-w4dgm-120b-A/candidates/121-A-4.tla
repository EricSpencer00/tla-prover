---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* A finite-extent version of Nat, used to bound model checking of the
\* character set itself.  Redefining Nat is how the .cfg file injects it.
Nat == CharacterSet

\* The failure function array is oversized (2*len) because the algorithm
\* runs a doubled-loop over the circular string without modulo arithmetic.
VARIABLES input, slen, failfun, matchIdx, outer, bestOff, pc

vars == <<input, slen, failfun, matchIdx, outer, bestOff, pc>>

Sentinel == slen + 1

TypeInvariant ==
  /\ input \in [1..slen -> Nat]
  /\ slen \in Nat
  /\ failfun \in [0..(2 * slen) -> (Sentinel \union (1..slen))]
  /\ matchIdx \in (Sentinel \union (0..slen))
  /\ outer \in 0..(2 * slen)
  /\ bestOff \in 0..(slen - 1)
  /\ pc \in {"outer", "lookup", "inner", "update", "follow", "post", "done"}

Init ==
  /\ \E s \in [1..slen -> Nat] : input = s
  /\ slen = Len(input)
  /\ failfun = [i \in 0..(2 * slen) |-> slen + 1]
  /\ matchIdx = slen + 1
  /\ outer = 1
  /\ bestOff = 0
  /\ pc = "outer"

OuterLoop ==
  /\ pc = "outer"
  /\ IF outer < (2 * slen) THEN pc' = "lookup" ELSE pc' = "done"
  /\ UNCHANGED <<input, slen, failfun, matchIdx, outer, bestOff>>

Lookup ==
  /\ pc = "lookup"
  /\ matchIdx' = failfun[outer - 1]
  /\ pc' = "inner"
  /\ UNCHANGED <<input, slen, failfun, outer, bestOff>>

InnerLoop ==
  /\ pc = "inner"
  /\ \/ input[(outer % slen) + 1] # input[((outer + matchIdx) % slen) + 1]
     \/ matchIdx = slen + 1
  /\ pc' = "post"
  /\ UNCHANGED <<input, slen, failfun, matchIdx, outer, bestOff>>

Update ==
  /\ pc = "post"
  /\ input[(outer % slen) + 1] < input[((outer + matchIdx) % slen) + 1]
  /\ bestOff' = outer
  /\ pc' = "follow"
  /\ UNCHANGED <<input, slen, failfun, matchIdx, outer>>

\* Follow the KMP failure chain or reset it when it is exhausted.
Follow ==
  /\ pc = "follow"
  /\ IF matchIdx = slen + 1
       THEN failfun' = [failfun EXCEPT ![outer] = slen + 1]
       ELSE failfun' = [failfun EXCEPT ![outer] = matchIdx + 1]
  /\ pc' = "done"
  /\ UNCHANGED <<input, slen, matchIdx, outer, bestOff>>

Done ==
  /\ pc = "done"
  /\ outer' = outer + 1
  /\ pc' = "outer"
  /\ UNCHANGED <<input, slen, failfun, matchIdx, bestOff>>

Stutter == UNCHANGED vars

Next == OuterLoop \/ Lookup \/ InnerLoop \/ Update \/ Follow \/ Done \/ Stutter

Spec == Init /\ [][Next]_vars
        /\ WF_vars(OuterLoop) /\ WF_vars(Lookup) /\ WF_vars(InnerLoop)
        /\ WF_vars(Update) /\ WF_vars(Follow) /\ WF_vars(Done)

\* The lexicographically-minimal rotation is a global optimum, not a
\* local minimum: it is the unique smallest rotation, and for ties it
\* is the one with the smallest shift index.
Correctness ==
  /\ \A i \in 0..(slen - 1): \A j \in 0..(slen - 1):
       (Rot(i) = Rot(j)) => (i <= j)
  /\ \A i \in 0..(slen - 1): (Rot(i) = Rot(bestOff) => (i >= bestOff))
  /\ \A i \in 0..(slen - 1): Rot(bestOff) <= Rot(i)

Rot(k) == [i \in 1..slen |-> input[((i + k - 1) % slen) + 1]]

Termination == <>(pc = "done")
====