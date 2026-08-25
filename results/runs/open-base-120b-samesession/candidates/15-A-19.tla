---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, T, F

(***  Basic definitions  ***)
Proc == 1 .. N

Message == [type : {"ECHO"}, sender : Proc]

PossibleMsgs == { m \in Message : TRUE }  \* all possible ECHO messages

EchoFrom(p) == { q \in Proc : [type |-> "ECHO", sender |-> q] \in Recv[p] }

SentEchoSet == { q \in Proc : [type |-> "ECHO", sender |-> q] \in Sent }

(***  Variables  ***)
VARIABLES Correct, Loc, Recv, Sent

vars == <<Correct, Loc, Recv, Sent>>

(***  Initialization  ***)
Init ==
  \E InitRecSet \subseteq Proc :
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Sent = {}
    /\ Recv = [p \in Proc |-> {}]
    /\ Loc = [p \in Proc |
                IF p \in Correct THEN
                  IF p \in InitRecSet THEN "InitRec" ELSE "NoInit"
                ELSE "NoInit"]
    /\ InitRecSet \subseteq Correct

(***  Actions  ***)

(* Receive new messages (including arbitrary Byzantine ones) *)
Receive(p, new) ==
  /\ p \in Correct
  /\ new \subseteq PossibleMsgs \ Recv[p]
  /\ Loc' = Loc
  /\ Sent' = Sent
  /\ Recv' = [Recv EXCEPT ![p] = Recv[p] \cup new]
  /\ UNCHANGED Correct

(* A correct process that already has the INIT message accepts and echoes *)
InitRecAccept(p) ==
  /\ p \in Correct
  /\ Loc[p] = "InitRec"
  /\ Loc' = [Loc EXCEPT ![p] = "Accepted"]
  /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<Recv, Correct>>

(* Receive enough ECHOs (>= N-2T and < N-T) and send ECHO but do not accept yet *)
EchoThreshold1(p) ==
  /\ p \in Correct
  /\ Loc[p] = "NoInit"
  /\ LET cnt == Cardinality(EchoFrom(p)) IN cnt >= N - 2*T /\ cnt < N - T
  /\ ~([type |-> "ECHO", sender |-> p] \in Sent)
  /\ Loc' = [Loc EXCEPT ![p] = "EchoSent"]
  /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<Recv, Correct>>

(* Receive enough ECHOs (>= N-T) and send ECHO and accept *)
EchoThreshold2(p) ==
  /\ p \in Correct
  /\ Loc[p] = "NoInit"
  /\ Cardinality(EchoFrom(p)) >= N - T
  /\ ~([type |-> "ECHO", sender |-> p] \in Sent)
  /\ Loc' = [Loc EXCEPT ![p] = "Accepted"]
  /\ Sent' = Sent \cup { [type |-> "ECHO", sender |-> p] }
  /\ UNCHANGED <<Recv, Correct>>

(* Already sent ECHO, now enough ECHOs received to accept *)
AcceptAfterEcho(p) ==
  /\ p \in Correct
  /\ Loc[p] = "EchoSent"
  /\ Cardinality(EchoFrom(p)) >= N - T
  /\ Loc' = [Loc EXCEPT ![p] = "Accepted"]
  /\ UNCHANGED <<Sent, Recv, Correct>>

Next ==
  \/ \E p \in Correct, new : Receive(p, new)
  \/ \E p \in Correct : InitRecAccept(p)
  \/ \E p \in Correct : EchoThreshold1(p)
  \/ \E p \in Correct : EchoThreshold2(p)
  \/ \E p \in Correct : AcceptAfterEcho(p)

(***  Specification  ***)
Spec == Init /\ [][Next]_vars

(***  Invariants  ***)
TypeOK ==
  /\ Correct \subseteq Proc
  /\ Cardinality(Correct) = N - F
  /\ Loc \in [Proc -> {"NoInit","InitRec","EchoSent","Accepted"}]
  /\ Recv \in [Proc -> SUBSET Message]
  /\ Sent \subseteq Message
  /\ \A p \in Proc :
        IF p \in Correct THEN
          Loc[p] \in {"NoInit","InitRec","EchoSent","Accepted"}
        ELSE TRUE

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

(***  Temporal properties  ***)

(* If every correct process starts with the INIT message, eventually they all accept *)
CorrLtl ==
  [] ( ( \A p \in Correct : Loc[p] = "InitRec" ) => <> ( \A p \in Correct : Loc[p] = "Accepted" ) )

(* Relay: if any correct process accepts, eventually all correct processes accept *)
RelayLtl ==
  [] ( ( \E p \in Correct : Loc[p] = "Accepted" ) => <> ( \A p \in Correct : Loc[p] = "Accepted" ) )

(* Unforgeability: if no correct process has the INIT message initially, no correct ever accepts *)
UnforgLtl ==
  ( \A p \in Correct : Loc[p] = "NoInit" ) => [] ( \A p \in Correct : Loc[p] # "Accepted" )

====