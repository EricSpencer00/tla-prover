---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F

\* -------------------------------------------------------------------------
\* Sets and basic definitions
\* -------------------------------------------------------------------------
Proc == 1 .. N
Msg  == <<Proc, "ECHO">>   \* any tuple <<sender, "ECHO">>

AllMsgs == { <<p, "ECHO">> : p \in Proc }

NMinus2T == N - 2 * T
NMinusT  == N - T

\* -------------------------------------------------------------------------
\* Variables
\* -------------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, sent

\* pc values (control locations)
PcVals == {"Start0", "Start1", "Echo", "Accept"}

\* -------------------------------------------------------------------------
\* Helper definitions
\* -------------------------------------------------------------------------
EchoSenders(p) == { m[1] : m \in recv[p] }

EchoCount(p) == Cardinality(EchoSenders(p))

PossibleMsgs(p) ==
  sent
  \cup { <<f, "ECHO">> : f \in Faulty }

\* -------------------------------------------------------------------------
\* Initial state
\* -------------------------------------------------------------------------
Init ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> PcVals]
  /\ \A p \in Correct : pc[p] \in {"Start0", "Start1"}
  /\ recv = [p \in Proc |-> {}]
  /\ sent = {}

\* -------------------------------------------------------------------------
\* Actions
\* -------------------------------------------------------------------------
Receive ==
  \E p \in Correct :
    \E new \in SUBSET ( PossibleMsgs(p) \ recv[p] ) :
      /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
      /\ UNCHANGED <<Correct, Faulty, pc, sent>>

InitAccept ==
  \E p \in Correct :
    /\ pc[p] = "Start1"
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ sent' = sent \cup { <<p, "ECHO">> }
    /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoOnly ==
  \E p \in Correct :
    /\ pc[p] = "Start0"
    /\ EchoCount(p) >= NMinus2T
    /\ EchoCount(p) < NMinusT
    /\ pc' = [pc EXCEPT ![p] = "Echo"]
    /\ sent' = sent \cup { <<p, "ECHO">> }
    /\ UNCHANGED <<Correct, Faulty, recv>>

SendEchoAccept ==
  \E p \in Correct :
    /\ pc[p] = "Start0"
    /\ EchoCount(p) >= NMinusT
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ sent' = sent \cup { <<p, "ECHO">> }
    /\ UNCHANGED <<Correct, Faulty, recv>>

AcceptOnly ==
  \E p \in Correct :
    /\ pc[p] = "Echo"
    /\ EchoCount(p) >= NMinusT
    /\ pc' = [pc EXCEPT ![p] = "Accept"]
    /\ UNCHANGED <<Correct, Faulty, recv, sent>>

Next ==
  \/ Receive
  \/ InitAccept
  \/ SendEchoOnly
  \/ SendEchoAccept
  \/ AcceptOnly

\* -------------------------------------------------------------------------
\* Specification
\* -------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, recv, sent>>

\* -------------------------------------------------------------------------
\* Invariants
\* -------------------------------------------------------------------------
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Faulty = Proc \ Correct
  /\ pc \in [Proc -> PcVals]
  /\ recv \in [Proc -> SUBSET Msg]
  /\ sent \subseteq Msg

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Correct) = N - F
  /\ Cardinality(Faulty) = F

\* -------------------------------------------------------------------------
\* Temporal properties
\* -------------------------------------------------------------------------
CorrLtl ==
  [] ( ( \A p \in Correct : pc[p] = "Start1" )
        => <> ( \A p \in Correct : pc[p] = "Accept" ) )

RelayLtl ==
  [] ( ( \E p \in Correct : pc[p] = "Accept" )
        => <> ( \A p \in Correct : pc[p] = "Accept" ) )

UnforgLtl ==
  [] ( ( \A p \in Correct : pc[p] = "Start0" )
        => [] ( \A p \in Correct : pc[p] # "Accept" ) )
====