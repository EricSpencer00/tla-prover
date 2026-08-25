---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES Suspects, Timeout, LastHeard, Clock, Outbox

\* ----------------------------------------------------------------------
\* Message record (for readability)
\* ----------------------------------------------------------------------
Message == [type : {"alive"}, from : Proc, to : Proc]

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
IncLast(p) ==
  [q \in Proc |-> 
     IF q = p THEN 0
     ELSE IF LastHeard[p][q] < Timeout[p][q] THEN LastHeard[p][q] + 1
          ELSE LastHeard[p][q]]

IncAllLast(p) ==
  [q \in Proc |-> IF q = p THEN 0 ELSE LastHeard[p][q] + 1]

ResetLast(p, S) ==
  [q \in Proc |-> IF q \in S THEN 0 ELSE LastHeard[p][q]]

IncTimeout(p, S) ==
  [q \in Proc |-> IF q \in S THEN Timeout[p][q] + 1 ELSE Timeout[p][q]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Suspects = [p \in Proc |-> {}]
  /\ Timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
  /\ LastHeard = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE 0]]
  /\ Clock     = [p \in Proc |-> 0]
  /\ Outbox    = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions for a single process
\* ----------------------------------------------------------------------
Send(p) ==
  /\ p \in Proc
  /\ Clock[p] % SendPoint = 0
  /\ Clock[p] % PredictPoint # 0
  /\ Suspects' = Suspects
  /\ Timeout'   = Timeout
  /\ LastHeard' = [LastHeard EXCEPT ![p] = IncLast(p)]
  /\ Outbox'    = [Outbox EXCEPT ![p] = { [type |-> "alive", from |-> p, to |-> q] :
                                           q \in Proc \ {p} }]
  /\ Clock'     = [Clock EXCEPT ![p] = Clock[p] + 1]

Predict(p) ==
  /\ p \in Proc
  /\ Clock[p] % PredictPoint = 0
  /\ Clock[p] % SendPoint # 0
  /\ Suspects' = [Suspects EXCEPT ![p] = Suspects[p] \cup
                     { q \in Proc \ {p} : LastHeard[p][q] > Timeout[p][q] }]
  /\ Timeout'   = Timeout
  /\ LastHeard' = [LastHeard EXCEPT ![p] = IncAllLast(p)]
  /\ Outbox'    = Outbox
  /\ Clock'     = [Clock EXCEPT ![p] = Clock[p] + 1]

Receive(p) ==
  /\ p \in Proc
  /\ Clock[p] % SendPoint # 0
  /\ Clock[p] % PredictPoint # 0
  /\ \E S \subseteq Proc \ {p} :
        /\ \A s \in S : \E m \in Messages :
               /\ m.type = "alive"
               /\ m.from = s
               /\ m.to   = p
        /\ Suspects' = [Suspects EXCEPT ![p] = Suspects[p] \ S]
        /\ Timeout'   = [Timeout EXCEPT ![p] = IncTimeout(p, S \cap Suspects[p])]
        /\ LastHeard' = [LastHeard EXCEPT ![p] = ResetLast(p, S)]
        /\ Outbox'    = Outbox
        /\ Clock'     = [Clock EXCEPT ![p] = Clock[p] + 1]

ClockReset(p) ==
  /\ p \in Proc
  /\ Clock[p] >= SendPoint
  /\ Clock[p] >= PredictPoint
  /\ \A q \in Proc \ {p} : Clock[p] >= Timeout[p][q]
  /\ Suspects' = Suspects
  /\ Timeout'   = Timeout
  /\ LastHeard' = LastHeard
  /\ Outbox'    = Outbox
  /\ Clock'     = [Clock EXCEPT ![p] = 0]

\* ----------------------------------------------------------------------
\* Global next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E p \in Proc : Send(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : ClockReset(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<Suspects, Timeout, LastHeard, Clock, Outbox>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Suspects \in [Proc -> SUBSET Proc]
  /\ Timeout   \in [Proc -> [Proc -> Nat]]
  /\ LastHeard \in [Proc -> [Proc -> Nat]]
  /\ Clock     \in [Proc -> Nat]
  /\ Outbox    \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Required identifiers for the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS    == TypeOK
PROPERTIES    == {}

====