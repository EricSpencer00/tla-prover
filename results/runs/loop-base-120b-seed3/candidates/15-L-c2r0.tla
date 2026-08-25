---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1 .. N
Msg  == [type : {"ECHO"}, sender : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

vars == <<Correct, Faulty, pc, sent, recv>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NMinus2T == N - 2 * T
NMinusT  == N - T

EchoMsg(p) == [type |-> "ECHO", sender |-> p]

AllMsgs == sent \cup { EchoMsg(f) : f \in Faulty }

EchoSenders(p) == { m.sender : m \in recv[p] }

CntEcho(p) == Cardinality(EchoSenders(p))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \in SUBSET Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ \A p \in Faulty : pc[p] = "Byz"
    /\ \E InitSet \in SUBSET Correct :
          /\ pc = [p \in Proc |-> 
                IF p \in Faulty THEN "Byz"
                ELSE IF p \in InitSet THEN "Init1" ELSE "Init0"]
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ \E new \in SUBSET AllMsgs :
          /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
    /\ UNCHANGED <<Correct, Faulty, pc, sent>>

EchoStep(p) ==
    \/ /\ pc[p] = "Init1"
       /\ sent' = sent \cup { EchoMsg(p) }
       /\ pc'   = [pc EXCEPT ![p] = "Accept"]
       /\ UNCHANGED <<Correct, Faulty, recv>>
    \/ /\ pc[p] = "Init0"
       /\ CntEcho(p) >= NMinus2T
       /\ CntEcho(p) <  NMinusT
       /\ sent' = sent \cup { EchoMsg(p) }
       /\ pc'   = [pc EXCEPT ![p] = "Echo"]
       /\ UNCHANGED <<Correct, Faulty, recv>>
    \/ /\ pc[p] = "Init0"
       /\ CntEcho(p) >= NMinusT
       /\ sent' = sent \cup { EchoMsg(p) }
       /\ pc'   = [pc EXCEPT ![p] = "Accept"]
       /\ UNCHANGED <<Correct, Faulty, recv>>
    \/ /\ pc[p] = "Echo"
       /\ CntEcho(p) >= NMinusT
       /\ pc'   = [pc EXCEPT ![p] = "Accept"]
       /\ UNCHANGED <<Correct, Faulty, sent, recv>>

Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : EchoStep(p)
    \/ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"Init0","Init1","Echo","Accept","Byz"}]
    /\ \A p \in Correct : pc[p] \in {"Init0","Init1","Echo","Accept"}
    /\ \A p \in Faulty  : pc[p] = "Byz"
    /\ sent \subseteq { EchoMsg(p) : p \in Correct }
    /\ recv \in [Proc -> SUBSET { EchoMsg(p) : p \in Proc }]

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Temporal properties
\* ----------------------------------------------------------------------
AllInit   == \A p \in Correct : pc[p] = "Init1"
AllAccept == \A p \in Correct : pc[p] = "Accept"
AnyAccept == \E p \in Correct : pc[p] = "Accept"
AllNoInit == \A p \in Correct : pc[p] = "Init0"

CorrLtl  == [] ( AllInit => <> AllAccept )
RelayLtl == [] ( AnyAccept => <> AllAccept )
UnforgLtl == [] ( AllNoInit => [] ( ~AnyAccept ) )

\* ----------------------------------------------------------------------
\* Theorem (optional, for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====