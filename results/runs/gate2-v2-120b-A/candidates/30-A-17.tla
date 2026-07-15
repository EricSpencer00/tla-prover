---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

(*-----------------------------------------------------------------
  Constants (to be instantiated in the .cfg file)
-----------------------------------------------------------------*)
CONSTANT N               \* number of processes
CONSTANT T               \* maximum number of tolerated faults
CONSTANT F               \* bound on actual crashes
CONSTANT Values          \* finite totally ordered set of proposal values
CONSTANT Bottom          \* special value distinct from all Values

ASSUME PosN      == N > 0
ASSUME Tge0      == T >= 0
ASSUME Fge0      == F >= 0
ASSUME FleT      == F <= T
ASSUME TwoTltN   == 2 * T < N
ASSUME BottomNotInValues == Bottom \notin Values
ASSUME NonEmptyValues   == \E v \in Values : TRUE

(*-----------------------------------------------------------------
  Derived constants
-----------------------------------------------------------------*)
Proc == 1..N

(*-----------------------------------------------------------------
  Message definition
-----------------------------------------------------------------*)
MessageType == {"P1", "P2"}

Message == [type : MessageType,
            sender : Proc,
            prop : Values,
            est : Values \cup {Bottom}]

P1Msg(msg) == msg.type = "P1"
P2Msg(msg) == msg.type = "P2"

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    pc,                 \* control location per process
    prop,               \* proposed value per process
    view,               \* local view matrix: view[p][q] = value q sent to p
    est,                \* estimated value per process
    dec,                \* decision value per process
    crashed,            \* set of processes that have crashed
    sent,               \* set of all sent messages
    received            \* received[p] = set of messages p has received

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
MaxOfSet(s) == 
    IF s = {} THEN Bottom
    ELSE CHOOSE x \in s : \A y \in s : y <= x

ReceivedFromSet(p, t) ==
    { m.sender : m \in received[p] /\ m.type = t }

AtLeastNMinusTFrom(p, t) ==
    Cardinality(ReceivedFromSet(p, t)) >= N - T

AtLeastNMinusTSameEst(p) ==
    \E v \in Values :
        Cardinality( { m \in received[p] : P2Msg(m) /\ m.est = v } ) >= N - T

AllP2From(p) ==
    \A q \in Proc : \E m \in received[p] : P2Msg(m) /\ m.sender = q

P1Done(p) == pc[p] = "P2Broadcast"
P2Waiting(p) == pc[p] = "P2Wait"
Done(p) == pc[p] = "Done"
Choosing(p) == pc[p] = "Choosing"
Crashed(p) == p \in crashed

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ pc = [p \in Proc |-> "P1Broadcast"]
    /\ prop \in [p \in Proc |-> Values]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ dec = [p \in Proc |-> Bottom]
    /\ crashed = {}
    /\ sent = {}
    /\ received = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
P1Broadcast ==
    /\ \E p \in Proc :
        /\ pc[p] = "P1Broadcast"
        /\ pc' = [pc EXCEPT ![p] = "P1Wait"]
        /\ sent' = sent \cup { [type |-> "P1", sender |-> p,
                               prop |-> prop[p], est |-> Bottom] }
        /\ UNCHANGED <<prop, view, est, dec, crashed, received>>

P1Receive ==
    /\ \E p \in Proc :
        /\ \E m \in sent :
            /\ m.type = "P1"
            /\ ~ (m \in received[p])
            /\ pc[p] \in {"P1Wait", "P2Broadcast", "P2Wait", "Choosing", "Done"}
            /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
            /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
            /\ UNCHANGED <<pc, prop, est, dec, crashed, sent>>

P1Advance ==
    /\ \E p \in Proc :
        /\ pc[p] = "P1Wait"
        /\ AtLeastNMinusTFrom(p, "P1")
        /\ est' = [est EXCEPT ![p] = MaxOfSet( { view[p][q] : q \in Proc } )]
        /\ pc' = [pc EXCEPT ![p] = "P2Broadcast"]
        /\ UNCHANGED <<prop, view, dec, crashed, sent, received>>

P2Broadcast ==
    /\ \E p \in Proc :
        /\ pc[p] = "P2Broadcast"
        /\ pc' = [pc EXCEPT ![p] = "P2Wait"]
        /\ sent' = sent \cup { [type |-> "P2", sender |-> p,
                               prop |-> prop[p], est |-> est[p]] }
        /\ UNCHANGED <<prop, view, est, dec, crashed, received>>

P2Receive ==
    /\ \E p \in Proc :
        /\ \E m \in sent :
            /\ m.type = "P2"
            /\ ~ (m \in received[p])
            /\ pc[p] \in {"P2Wait", "Choosing", "Done"}
            /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
            /\ UNCHANGED <<pc, prop, view, est, dec, crashed, sent>>

DecideFromP2 ==
    /\ \E p \in Proc :
        /\ pc[p] = "P2Wait"
        /\ AtLeastNMinusTSameEst(p)
        /\ \E v \in Values :
            /\ Cardinality( { m \in received[p] : P2Msg(m) /\ m.est = v } ) >= N - T
            /\ dec' = [dec EXCEPT ![p] = v]
            /\ pc' = [pc EXCEPT ![p] = "Done"]
        /\ UNCHANGED <<prop, view, est, crashed, sent, received>>

AllP2ButNoDecision ==
    /\ \E p \in Proc :
        /\ pc[p] = "P2Wait"
        /\ AllP2From(p)
        /\ ~AtLeastNMinusTSameEst(p)
        /\ pc' = [pc EXCEPT ![p] = "Choosing"]
        /\ UNCHANGED <<prop, view, est, dec, crashed, sent, received>>

ChooseAndDecide ==
    /\ \E p \in Proc :
        /\ pc[p] = "Choosing"
        /\ \E v \in Values :
            /\ v \in { view[p][q] : q \in Proc }
            /\ dec' = [dec EXCEPT ![p] = v]
            /\ pc' = [pc EXCEPT ![p] = "Done"]
        /\ UNCHANGED <<prop, view, est, crashed, sent, received>>

Crash ==
    /\ \E p \in Proc :
        /\ ~Crashed(p)
        /\ Cardinality(crashed) < F
        /\ crashed' = crashed \cup {p}
        /\ pc' = [pc EXCEPT ![p] = "Crashed"]
        /\ UNCHANGED <<prop, view, est, dec, sent, received>>

Next ==
    \/ P1Broadcast
    \/ P1Receive
    \/ P1Advance
    \/ P2Broadcast
    \/ P2Receive
    \/ DecideFromP2
    \/ AllP2ButNoDecision
    \/ ChooseAndDecide
    \/ Crash

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<pc, prop, view, est, dec, crashed, sent, received>>

(*-----------------------------------------------------------------
  Type correctness invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> {"P1Broadcast", "P1Wait",
                        "P2Broadcast", "P2Wait",
                        "Choosing", "Done", "Crashed"}]
    /\ prop \in [Proc -> Values]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ dec \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \subseteq Proc
    /\ sent \subseteq { [type |-> t, sender |-> p, prop |-> v, est |-> e] :
                        t \in MessageType,
                        p \in Proc,
                        v \in Values,
                        e \in (Values \cup {Bottom}) }
    /\ received \in [Proc -> SUBSET sent]

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
Validity ==
    \A p \in Proc :
        (dec[p] # Bottom) => \E q \in Proc : prop[q] = dec[p]

Agreement ==
    \A p, q \in Proc :
        (dec[p] # Bottom) /\ (dec[q] # Bottom) => dec[p] = dec[q]

====