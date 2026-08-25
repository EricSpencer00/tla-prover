---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  CONSTANTS
--------------------------------------------------------------------*)
CONSTANTS
    Proc,            \* Set of process identifiers
    d0,              \* Default timeout interval (positive integer)
    SendPoint,       \* Positive integer: period for sending alive msgs
    PredictPoint,    \* Positive integer: period for making predictions
    Messages         \* Superset of all possible messages (including alive)

(*--------------------------------------------------------------------
  MESSAGE DEFINITION
--------------------------------------------------------------------*)
AliveMsg(p, q) == [type |-> "alive", from |-> p, to |-> q]

(*--------------------------------------------------------------------
  STATE VARIABLES
--------------------------------------------------------------------*)
VARIABLES
    Suspect,   \* [p \in Proc -> SUBSET Proc]   : processes p suspects
    Timeout,   \* [p \in Proc -> [q \in Proc \ {p} -> Nat]] : timeout interval for each peer
    Last,      \* [p \in Proc -> [q \in Proc \ {p} -> Nat]] : ticks since last alive from q
    Clock,     \* [p \in Proc -> Nat]          : local clock of each process
    Outgoing   \* [p \in Proc -> SUBSET Messages] : messages p intends to send

vars == << Suspect, Timeout, Last, Clock, Outgoing >>

(*--------------------------------------------------------------------
  HELPER DEFINITIONS
--------------------------------------------------------------------*)
IsSend(t) == (t % SendPoint = 0) /\ (t % PredictPoint # 0)
IsPredict(t) == (t % PredictPoint = 0) /\ (t % SendPoint # 0)

AllPeers(p) == Proc \ {p}

IncLastExcept(p, keep) ==
    [Last EXCEPT ![p] = [q \in DOMAIN Last[p] |-> 
         IF q \in keep THEN 0 ELSE @ + 1]]

IncLastAll(p) ==
    [Last EXCEPT ![p] = [q \in DOMAIN Last[p] |-> @ + 1]]

ResetClock(p) ==
    IF Clock[p] >= MaxClock THEN 0 ELSE Clock[p] + 1

MaxClock == SendPoint * PredictPoint   \* a finite bound guaranteeing reset

(*--------------------------------------------------------------------
  INITIAL STATE
--------------------------------------------------------------------*)
Init ==
    /\ Suspect = [p \in Proc |-> {}]
    /\ Timeout = [p \in Proc |-> [q \in AllPeers(p) |-> d0]]
    /\ Last    = [p \in Proc |-> [q \in AllPeers(p) |-> 0]]
    /\ Clock   = [p \in Proc |-> 0]
    /\ Outgoing = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  SEND ACTION (alive messages)
--------------------------------------------------------------------*)
Send(p) ==
    LET peers == AllPeers(p) IN
    /\ IsSend(Clock[p])
    /\ Outgoing' = [Outgoing EXCEPT ![p] = { AliveMsg(p, q) : q \in peers }]
    /\ Suspect' = Suspect
    /\ Timeout' = Timeout
    /\ Last'    = IncLastAll(p)   \* increment counters for all peers
    /\ Clock'   = [Clock EXCEPT ![p] = ResetClock(p)]
    /\ UNCHANGED << Suspect, Timeout, Last, Outgoing >> \* other processes unchanged

(*--------------------------------------------------------------------
  PREDICT ACTION (update suspicion set)
--------------------------------------------------------------------*)
Predict(p) ==
    LET peers == AllPeers(p) IN
    /\ IsPredict(Clock[p])
    /\ Suspect' = [Suspect EXCEPT ![p] = 
           Suspect[p] \cup { q \in peers : Last[p][q] > Timeout[p][q] }]
    /\ Timeout' = Timeout
    /\ Last'    = IncLastAll(p)
    /\ Clock'   = [Clock EXCEPT ![p] = ResetClock(p)]
    /\ Outgoing' = Outgoing
    /\ UNCHANGED << Suspect, Timeout, Last, Outgoing >> \* other processes unchanged

(*--------------------------------------------------------------------
  RECEIVE ACTION (process incoming alive messages)
--------------------------------------------------------------------*)
Receive(p) ==
    LET peers == AllPeers(p) IN
    \* nondeterministically choose a set of peers from which p receives an alive
    \* message in this step
    \E recvSet \in SUBSET peers :
        /\ ~IsSend(Clock[p])
        /\ ~IsPredict(Clock[p])
        /\ Outgoing' = Outgoing
        /\ Clock'   = [Clock EXCEPT ![p] = ResetClock(p)]
        /\ Suspect' = [Suspect EXCEPT ![p] = Suspect[p] \ { recvSet }]
        /\ Timeout' = [Timeout EXCEPT ![p] =
                [q \in AllPeers(p) |-> 
                    IF q \in recvSet /\ q \in Suspect[p] 
                    THEN Timeout[p][q] + 1 
                    ELSE @]]
        /\ Last'    = IncLastExcept(p, recvSet)
        /\ UNCHANGED << Suspect, Timeout, Last, Outgoing >> \* other processes unchanged

(*--------------------------------------------------------------------
  NEXT STATE RELATION
--------------------------------------------------------------------*)
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

(*--------------------------------------------------------------------
  TYPE INVARIANT
--------------------------------------------------------------------*)
TypeOK ==
    /\ Suspect \in [Proc -> SUBSET Proc]
    /\ Timeout \in [Proc -> [q \in Proc \ {#} -> Nat]]
    /\ Last    \in [Proc -> [q \in Proc \ {#} -> Nat]]
    /\ Clock   \in [Proc -> Nat]
    /\ Outgoing \in [Proc -> SUBSET Messages]

(*--------------------------------------------------------------------
  SPECIFICATION
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

====