---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

(*=============================================================================
  Constants
 =============================================================================*)
CONSTANTS N, T, F

(*=============================================================================
  Basic definitions
 =============================================================================*)
Proc == 1..N

Msg == { [type |-> "ECHO", from |-> p] : p \in Proc }

EchoMsg(p) == [type |-> "ECHO", from |-> p]

(*=============================================================================
  Variables
 =============================================================================*)
VARIABLES Correct, Faulty, pc, recv, Sent

(*=============================================================================
  Helper functions
 =============================================================================*)
CountDistinctEcho(p) == Cardinality({ m.from : m \in recv[p] })

(*=============================================================================
  Initial state
 =============================================================================*)
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"InitYes", "InitNo", "Echo", "Accept"}]
    /\ \A p \in Correct : pc[p] \in {"InitYes", "InitNo"}
    /\ Sent = {}
    /\ recv = [p \in Proc |-> {}]

(*=============================================================================
  Actions
 =============================================================================*)
Receive(p) ==
    /\ p \in Correct
    /\ LET Possible == Sent \cup { EchoMsg(q) : q \in Faulty } IN
       \E new \in SUBSET (Possible \ recv[p]) :
          /\ recv' = [recv EXCEPT ![p] = @ \cup new]
          /\ UNCHANGED <<Correct, Faulty, pc, Sent>>

SendEcho(p) ==
    LET cnt == CountDistinctEcho(p) IN
    /\ p \in Correct
    /\ EchoMsg(p) \notin Sent
    /\ ( pc[p] = "InitYes"
          \/ (pc[p] = "InitNo" /\ cnt >= N - 2*T /\ cnt < N - T)
          \/ (pc[p] = "InitNo" /\ cnt >= N - T)
          \/ (pc[p] = "Echo"   /\ cnt >= N - T) )
    /\ Sent' = Sent \cup { EchoMsg(p) }
    /\ pc' = [pc EXCEPT ![p] =
                IF pc[p] = "InitYes" THEN "Accept"
                ELSE IF pc[p] = "InitNo" /\ cnt >= N - T THEN "Accept"
                ELSE IF pc[p] = "InitNo" /\ cnt >= N - 2*T /\ cnt < N - T THEN "Echo"
                ELSE IF pc[p] = "Echo"   /\ cnt >= N - T THEN "Accept"
                ELSE pc[p] ]
    /\ UNCHANGED <<Correct, Faulty, recv>>

Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : SendEcho(p)

(*=============================================================================
  Specification
 =============================================================================*)
Spec == Init /\ [][Next]_<<Correct, Faulty, pc, recv, Sent>>

(*=============================================================================
  Invariants
 =============================================================================*)
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"InitYes","InitNo","Echo","Accept"}]
    /\ Sent \subseteq { EchoMsg(p) : p \in Correct }
    /\ recv \in [Proc -> SUBSET Msg]

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

(*=============================================================================
  LTL properties
 =============================================================================*)
CorrLtl == ( \A p \in Correct : pc[p] = "InitYes" ) => <> ( \A p \in Correct : pc[p] = "Accept" )

RelayLtl == [] ( ( \E p \in Correct : pc[p] = "Accept" ) => <> ( \A p \in Correct : pc[p] = "Accept" ) )

UnforgLtl == ( \A p \in Correct : pc[p] = "InitNo" ) => [] ( \A p \in Correct : pc[p] # "Accept" )
====