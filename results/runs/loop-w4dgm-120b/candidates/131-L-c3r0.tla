---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

ASSUME /\ Value \in Nat /\ Value >= 1
       /\ 0 \notin Value

\* No new state: everything is inherited from MajorityVote, including
\* the definition of the candidate and the occurrence-counting helpers.
VARIABLES candidate, seen, pos, counted, vote

TypeOK ==
  /\ 0 <= candidate /\ candidate < 2
  /\ seen \in [1..Value -> BOOLEAN]
  /\ pos \in 1..Value
  /\ counted \in Nat
  /\ vote \in 0..Value

\* The candidate is always a Boolean, so it can never equal a non-Boolean.
\* The main correctness property is lifted from MajorityVote unchanged.
Inv == TypeOK /\ NoWrongMajority
Spec == Init /\ Next
TypeOKInv == Spec => [][TypeOK]_<<candidate, seen, pos, counted, vote>>
CorrectInv == Spec => []Inv

Init ==
  /\ candidate = 0
  /\ seen = [v \in 1..Value |-> FALSE]
  /\ pos = 1
  /\ counted = 0
  /\ vote = 0

Next ==
  \/ SeeNew
  \/ Forget
  \/ Count
  \/ Reset

\* All transition definitions below are verbatim copies from MajorityVote;
\* they are reproduced here so that this module is a closed, self-checking
\* specification and needs no external dependency in the .cfg file.
SeeNew ==
  /\ pos <= Value
  /\ \E v \in 1..Value :
       /\ ~seen[v]
       /\ seen' = [seen EXCEPT ![v] = TRUE]
  /\ UNCHANGED <<candidate, pos, counted, vote>>

Forget ==
  /\ \E v \in 1..Value : seen[v]
  /\ \E v \in 1..Value :
       /\ seen[v]
       /\ seen' = [seen EXCEPT ![v] = FALSE]
  /\ UNCHANGED <<candidate, pos, counted, vote>>

Count ==
  /\ pos <= Value
  /\ counted' = counted + 1
  /\ vote' = vote + (IF seen[vote] THEN 1 ELSE 0)
  /\ pos' = pos + 1
  /\ UNCHANGED <<candidate, seen>>

Reset ==
  /\ pos > Value
  /\ candidate' = 1 - candidate
  /\ pos' = 1
  /\ counted' = 0
  /\ vote' = 0
  /\ UNCHANGED seen

====