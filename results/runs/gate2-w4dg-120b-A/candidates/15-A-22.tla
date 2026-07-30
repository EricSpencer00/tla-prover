---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Validation: these constants must satisfy the algorithm's assumptions.
RECURSIVE SumCon(_)
SumCon(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN x + SumCon(S \ {x})

VARIABLES correct, faulty, PC, rcvd, sent

vars == << correct, faulty, PC, rcvd, sent >>
Msgs == {"ECHO"}
Admins == 0..(N - 1)
Quiet == 0
Expects == 1
Echoed == 2
Accepted == 3

TypeOK ==
  /\ correct \subseteq Admins
  /\ faulty \subseteq Admins
  /\ PC \in [Admins -> {Quiet, Expects, Echoed, Accepted}]
  /\ rcvd \in [Admins -> SUBSET (Admins \X Msgs)]
  /\ sent \in SUBSET (Admins \X Msgs)

Init ==
  /\ SumCon({N - Cardinality(S) : S \in SUBSET Admins : Cardinality(S) = N - F}) = N
  /\ correct = {i \in Admins : rcvd[i] = {}}
  /\ faulty = Admins \ correct
  /\ PC = [i \in Admins |-> Quiet]
  /\ rcvd = [i \in Admins |-> {}]
  /\ sent = {}

QuietInit ==
  /\ SumCon({N - Cardinality(S) : S \in SUBSET Admins : Cardinality(S) = N - F}) = N
  /\ correct = {}
  /\ faulty = Admins
  /\ PC = [i \in Admins |-> Quiet]
  /\ rcvd = [i \in Admins |-> {}]
  /\ sent = {}

Receive(i, M) ==
  /\ i \in correct
  /\ M # {}
  /\ M \subseteq (sent \cup (faulty \X Msgs))
  /\ rcvd' = [rcvd EXCEPT ![i] = M]
  /\ UNCHANGED << correct, faulty, PC, sent >>

\* A correct process that received the broadcaster's INIT message accepts immediately.
ActOnInit(i) ==
  /\ i \in correct
  /\ PC[i] = Quiet
  /\ rcvd[i] = {}
  /\ PC' = [PC EXCEPT ![i] = Accepted]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED << correct, faulty, rcvd >>

ActOnSome(i) ==
  /\ i \in correct
  /\ PC[i] \in {Quiet, Expects}
  /\ Cardinality({j \in Admins : <<j, "ECHO">> \in rcvd[i]}) >= N - 2 * T
  /\ Cardinality({j \in Admins : <<j, "ECHO">> \in rcvd[i]}) < N - T
  /\ PC' = [PC EXCEPT ![i] = Echoed]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED << correct, faulty, rcvd >>

ActOnMany(i) ==
  /\ i \in correct
  /\ PC[i] \in {Quiet, Expects}
  /\ Cardinality({j \in Admins : <<j, "ECHO">> \in rcvd[i]}) >= N - T
  /\ PC' = [PC EXCEPT ![i] = Accepted]
  /\ sent' = sent \cup {<<i, "ECHO">>}
  /\ UNCHANGED << correct, faulty, rcvd >>

ActOnEcho(i) ==
  /\ i \in correct
  /\ PC[i] = Echoed
  /\ Cardinality({j \in Admins : <<j, "ECHO">> \in rcvd[i]}) >= N - T
  /\ PC' = [PC EXCEPT ![i] = Accepted]
  /\ UNCHANGED << correct, faulty, rcvd, sent >>

Next ==
  \/ \E i \in Admins, M \in SUBSET (Admins \X Msgs) : Receive(i, M)
  \/ \E i \in Admins : ActOnInit(i)
  \/ \E i \in Admins : ActOnSome(i)
  \/ \E i \in Admins : ActOnMany(i)
  \/ \E i \in Admins : ActOnEcho(i)

Spec == Init /\ [][Next]_vars

CorrLtl == (Sent == {}) ~> (forall i \in Admins : PC[i] = Accepted)
RelayLtl == (Sent # {}) ~> (forall i \in Admins : PC[i] = Accepted)

\* Unforgeability: if no correct process broadcasts (all start in the non-broadcast
\* state), no correct process ever accepts.
FCConstraints == (correct = {}) => (forall i \in correct : PC[i] = Quiet)

UnforgLtl ==
  (correct = {}) ~> (forall i \in Admins : PC[i] = Accepted)

====