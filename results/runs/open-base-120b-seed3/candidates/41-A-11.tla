---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    Suspicion,   \* [p \in Proc |-> SUBSET Proc]
    Timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]
    LastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]]
    Clock,       \* [p \in Proc |-> Nat]
    Outgoing     \* [p \in Proc |-> SUBSET Messages]

vars == << Suspicion, Timeout, LastHeard, Clock, Outgoing >>

\* ----------------------------------------------------------------------
\* Message definition (must be a subset of the declared constant Messages)
\* ----------------------------------------------------------------------
Message == [type : {"alive"}, from : Proc, to : Proc]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Suspicion = [p \in Proc |-> {}]
    /\ Timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ LastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock     = [p \in Proc |-> 0]
    /\ Outgoing   = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SendEnabled(p)    == (Clock[p] % SendPoint = 0) /\ (Clock[p] % PredictPoint # 0)
PredictEnabled(p) == (Clock[p] % PredictPoint = 0) /\ (Clock[p] % SendPoint # 0)

AllOthers(p) == Proc \ {p}

AliveMsg(p,q) == [type |-> "alive", from |-> p, to |-> q]

\* ----------------------------------------------------------------------
\* Send action for a process p
\* ----------------------------------------------------------------------
Send(p) ==
    /\ SendEnabled(p)
    /\ \* create alive messages for every other process
       let newMsgs == { AliveMsg(p, q) : q \in AllOthers(p) } in
       /\ Outgoing' = [Outgoing EXCEPT ![p] = @ \cup newMsgs]
    /\ \* increment clock and all last‑heard counters (except self)
       Clock'     = [Clock EXCEPT ![p] = @ + 1]
    /\ LastHeard' = [LastHeard EXCEPT
                        ![p] = [q \in AllOthers(p) |-> @[q] + 1],
                        ![p][p] = @]   \* self entry unchanged
    /\ UNCHANGED << Suspicion, Timeout >>

\* ----------------------------------------------------------------------
\* Predict action for a process p
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ PredictEnabled(p)
    /\ \* add to suspicion any process q whose counter exceeds its timeout
       let newlySuspected == { q \in AllOthers(p) :
                                 LastHeard[p][q] > Timeout[p][q] } in
       Suspicion' = [Suspicion EXCEPT ![p] = @ \cup newlySuspected]
    /\ Clock'     = [Clock EXCEPT ![p] = @ + 1]
    /\ LastHeard' = [LastHeard EXCEPT
                        ![p] = [q \in AllOthers(p) |-> @[q] + 1],
                        ![p][p] = @]
    /\ UNCHANGED << Timeout, Outgoing >>

\* ----------------------------------------------------------------------
\* Receive action for a process p
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ ~SendEnabled(p)
    /\ ~PredictEnabled(p)
    /\ \* set of alive messages addressed to p that are received this step
       \E recSet \subseteq { m \in Messages : 
                              /\ m.type = "alive"
                              /\ m.to   = p } :
         /\ \* update outgoing for p (no new outgoing messages)
            Outgoing' = [Outgoing EXCEPT ![p] = @]
         /\ \* reset counters for senders whose message was received,
            /\ remove them from suspicion, and possibly adapt timeout
            let senders == { m.from : m \in recSet } in
               /\ LastHeard' = [LastHeard EXCEPT
                                   ![p] = [q \in AllOthers(p) |
                                            IF q \in senders
                                            THEN 0
                                            ELSE @[q]]]
               /\ Suspicion' = [Suspicion EXCEPT
                                   ![p] = @ \setminus senders]
               /\ Timeout'   = [Timeout EXCEPT
                                   ![p] = [q \in AllOthers(p) |
                                            IF q \in senders /\ q \in @
                                            THEN @[q] + 1
                                            ELSE @[q]]]
         /\ Clock' = [Clock EXCEPT ![p] = @ + 1]
         /\ UNCHANGED << >>)   \* all other variables unchanged

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Suspicion \in [Proc -> SUBSET Proc]
    /\ Timeout   \in [Proc -> [Proc -> Nat]]
    /\ LastHeard \in [Proc -> [Proc -> Nat]]
    /\ Clock     \in [Proc -> Nat]
    /\ Outgoing   \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : p \notin Suspicion[p]    \* a process never suspects itself

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
Init == Init
Next == Next
TypeOK == TypeOK
Spec == Spec

====