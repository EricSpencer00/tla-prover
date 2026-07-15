---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS N, T, F, Values, Bottom

(*-----------------------------------------------------------------
  Derived sets and helper definitions
-----------------------------------------------------------------*)
Proc == 1..N

MessageType == {"phase1", "phase2"}

(* A message consists of a type, a sender, a proposed value, and
   an estimated value (only used for phase2). *)
Message == [type : MessageType,
            sender : Proc,
            prop  : Values,
            est   : Values \cup {Bottom}]

(*-----------------------------------------------------------------
  Variables
-----------------------------------------------------------------*)
VARIABLES
    pc,          \* control location of each process
    propVals,    \* proposed value of each process
    localViews,  \* N-by-N matrix: localViews[p][q] is the value p knows about q
    estVals,     \* estimated value after phase1
    decision,    \* decision value (Bottom if none)
    crashCount,  \* number of crashed processes
    sent,        \* set of all messages that have been broadcast
    received     \* received[p] is the set of messages received by p

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
    /\ pc = [p \in Proc |-> "broadcast1"]
    /\ propVals \in [p \in Proc |-> Values]
    /\ localViews = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ estVals = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashCount = 0
    /\ sent = {}
    /\ received = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Max(S) ==
    IF S = {} THEN Bottom
    ELSE CHOOSE x \in S : \A y \in S : y <= x

ReceivedFrom(p, typ) ==
    { m.prop : m \in received[p] /\ m.type = typ }

ReceivedPhase2Est(p) ==
    { m.est : m \in received[p] /\ m.type = "phase2" /\ m.est # Bottom }

EnoughDistinct(mset) ==
    Cardinality(mset) >= N - T

SameEstThreshold(p) ==
    \E v \in Values :
        Cardinality({ m \in received[p] : m.type = "phase2" /\ m.est = v }) >= N - T

AllSendersReceived(p) ==
    \A q \in Proc :
        \E m \in received[p] : m.sender = q

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)

BroadcastPhase1(p) ==
    /\ pc[p] = "broadcast1"
    /\ sent' = sent \cup { [type |-> "phase1",
                           sender |-> p,
                           prop |-> propVals[p],
                           est |-> Bottom] }
    /\ pc' = [pc EXCEPT ![p] = "wait1"]
    /\ UNCHANGED <<propVals, localViews, estVals,
                    decision, crashCount, received>>

ReceivePhase1(p) ==
    /\ pc[p] = "wait1"
    /\ \E m \in sent :
          /\ m.type = "phase1"
          /\ m.sender \in Proc
          /\ localViews[p][m.sender] = Bottom
    /\ localViews' = [localViews EXCEPT ![p][m.sender] = m.prop]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<pc, propVals, estVals, decision,
                    crashCount, sent>>

ComputeEst(p) ==
    /\ pc[p] = "wait1"
    /\ Cardinality(ReceivedFrom(p, "phase1")) >= N - T
    /\ estVals' = [estVals EXCEPT ![p] = Max({ localViews[p][q] : q \in Proc })]
    /\ pc' = [pc EXCEPT ![p] = "broadcast2"]
    /\ UNCHANGED <<propVals, localViews, decision,
                    crashCount, sent, received>>

BroadcastPhase2(p) ==
    /\ pc[p] = "broadcast2"
    /\ sent' = sent \cup { [type |-> "phase2",
                           sender |-> p,
                           prop |-> propVals[p],
                           est |-> estVals[p]] }
    /\ pc' = [pc EXCEPT ![p] = "wait2"]
    /\ UNCHANGED <<propVals, localViews, estVals,
                    decision, crashCount, received>>

ReceivePhase2(p) ==
    /\ pc[p] = "wait2"
    /\ \E m \in sent :
          /\ m.type = "phase2"
          /\ m.sender \in Proc
          /\ \A r \in received[p] : ~ (r.type = "phase2" /\ r.sender = m.sender)
    /\ received' = [received EXCEPT ![p] = received[p] \cup {m}]
    /\ UNCHANGED <<pc, propVals, localViews, estVals,
                    decision, crashCount, sent>>

DecideByThreshold(p) ==
    /\ pc[p] = "wait2"
    /\ SameEstThreshold(p)
    /\ \E v \in Values :
          /\ Cardinality({ m \in received[p] : m.type = "phase2" /\ m.est = v }) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<propVals, localViews, estVals,
                    crashCount, sent, received>>

MoveToChoosing(p) ==
    /\ pc[p] = "wait2"
    /\ AllSendersReceived(p)
    /\ ~SameEstThreshold(p)
    /\ pc' = [pc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<propVals, localViews, estVals,
                    decision, crashCount, sent, received>>

ChooseAndDecide(p) ==
    /\ pc[p] = "choosing"
    /\ decision' = [decision EXCEPT ![p] = 
          CHOOSE v \in Values :
            \E q \in Proc : localViews[p][q] = v]
    /\ pc' = [pc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<propVals, localViews, estVals,
                    crashCount, sent, received>>

Crash(p) ==
    /\ pc[p] # "crash"
    /\ crashCount < F
    /\ pc' = [pc EXCEPT ![p] = "crash"]
    /\ crashCount' = crashCount + 1
    /\ UNCHANGED <<propVals, localViews, estVals,
                    decision, sent, received>>

Next ==
    \/ \E p \in Proc : BroadcastPhase1(p)
    \/ \E p \in Proc : ReceivePhase1(p)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : BroadcastPhase2(p)
    \/ \E p \in Proc : ReceivePhase2(p)
    \/ \E p \in Proc : DecideByThreshold(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : ChooseAndDecide(p)
    \/ \E p \in Proc : Crash(p)

Spec == Init /\ [][Next]_<<pc, propVals, localViews, estVals,
                decision, crashCount, sent, received>>

(*-----------------------------------------------------------------
  Invariants
-----------------------------------------------------------------*)
TypeOK ==
    /\ pc \in [Proc -> {"broadcast1","wait1",
                        "broadcast2","wait2",
                        "done","crash","choosing"}]
    /\ propVals \in [Proc -> Values]
    /\ localViews \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ estVals \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashCount \in Nat
    /\ sent \subseteq Message
    /\ received \in [Proc -> SUBSET Message]

Validity ==
    \A p \in Proc :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

=============================================================================