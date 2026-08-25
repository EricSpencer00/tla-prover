---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"ECHO"}, from : Proc]

ECHO(p) == [type |-> "ECHO", from |-> p]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, Sent, Recv

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Senders(mset) == { m.from : m ∈ mset }

Cnt(p) == Cardinality(Senders(Recv[p]))

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ \* each correct process nondeterministically starts with or without INIT
     \E initChoice \in [Correct -> BOOLEAN] :
        pc = [p \in Correct |-> IF initChoice[p] THEN "Init" ELSE "NoInit"]
  /\ Sent = {}
  /\ Recv = [p \in Correct |-> {}]

\* ----------------------------------------------------------------------
\* Action of a single correct process p
\* ----------------------------------------------------------------------
Action(p) ==
  /\ p \in Correct
  /\ \E new \subseteq (Sent \cup {ECHO(q) : q \in Faulty}) :
        LET Recv' == [Recv EXCEPT ![p] = Recv[p] \cup new] IN
        LET cnt  == Cardinality(Senders(Recv')) IN
        CASE
          pc[p] = "Init" ->
            /\ pc' = [pc EXCEPT ![p] = "Accepted"]
            /\ Sent' = Sent \cup {ECHO(p)}
            /\ Recv' = Recv'
          pc[p] = "NoInit" /\ cnt >= N - T ->
            /\ pc' = [pc EXCEPT ![p] = "Accepted"]
            /\ Sent' = Sent \cup {ECHO(p)}
            /\ Recv' = Recv'
          pc[p] = "NoInit" /\ cnt >= N - 2*T /\ cnt < N - T ->
            /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
            /\ Sent' = Sent \cup {ECHO(p)}
            /\ Recv' = Recv'
          pc[p] = "EchoSent" /\ cnt >= N - T ->
            /\ pc' = [pc EXCEPT ![p] = "Accepted"]
            /\ Sent' = Sent
            /\ Recv' = Recv'
          OTHER -> 
            /\ UNCHANGED <<pc, Sent, Recv>>
        END

\* ----------------------------------------------------------------------
\* Combined step for any correct process
\* ----------------------------------------------------------------------
ReceiveAct == \E p \in Correct : Action(p)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ ReceiveAct
  \/ UNCHANGED <<pc, Sent, Recv>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\
  [][Next]_<<pc, Sent, Recv>> /\
  WF_<<pc, Sent, Recv>>(ReceiveAct)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Correct -> {"NoInit", "Init", "EchoSent", "Accepted"}]
  /\ Sent \subseteq {ECHO(p) : p \in Correct}
  /\ Recv \in [Correct -> SUBSET {ECHO(q) : q \in Proc}]

\* ----------------------------------------------------------------------
\* Fault‑containment constraints
\* ----------------------------------------------------------------------
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == ( \A p \in Correct : pc[p] = "Init" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl == ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl == ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* Theorem statements (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====