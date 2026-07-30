---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES want, ticket, inCS, done
vars == <<want, ticket, inCS, done>>

Processes == 1..N
MinNat == 0

TypeOK ==
  /\ want \in [Processes -> BOOLEAN]
  /\ ticket \in [Processes -> MinNat..MaxNat]
  /\ inCS \in [Processes -> BOOLEAN]
  /\ done \in 0..N

Init ==
  /\ want = [p \in Processes |-> FALSE]
  /\ ticket = [p \in Processes |-> MinNat]
  /\ inCS = [p \in Processes |-> FALSE]
  /\ done = 0

Request(p) ==
  /\ ~want[p]
  /\ \A q \in Processes : ~want[q]
  /\ \A q \in Processes : ticket[q] # MaxNat
  /\ want' = [want EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = MaxNat]
  /\ UNCHANGED <<inCS, done>>

Enter(p) ==
  /\ want[p]
  /\ \A q \in Processes : inCS[q] => ticket[q] <= ticket[p]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<want, ticket, done>>

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ want' = [want EXCEPT ![p] = FALSE]
  /\ ticket' = [ticket EXCEPT ![p] = MinNat]
  /\ done' = IF done < N THEN done + 1 ELSE done

Next ==
  \/ \E p \in Processes : Request(p)
  \/ \E p \in Processes : Enter(p)
  \/ \E p \in Processes : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in Processes : (inCS[p] /\ inCS[q]) => (p = q)

Inv == TypeOK /\ MutualExclusion

NatOverride == Nat
====