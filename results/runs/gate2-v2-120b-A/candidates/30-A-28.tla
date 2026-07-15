---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(* ----------------------------------------------------------------------
   Constants (must be provided in the .cfg)
   ---------------------------------------------------------------------- *)
CONSTANTS N, T, F, Values, Bottom

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
Proc == 1..N
MessageType == {"Phase1", "Phase2"}
Message == [type : MessageType,
            sender : Proc,
            value : Values,
            est : Values \cup {Bottom}]

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES loc,          \* control location of each process
          localView,    \* N x N matrix of observed values
          prop,         \* proposed value of each process
          est,          \* estimated value after phase 1
          decision,    \* decided value (Bottom = not decided)
          crashed,     \* number of crashed processes
          sent,         \* set of all messages that have been sent
          recv          \* messages received by each process

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
Locs == {"Broadcast1", "Wait1", "Broadcast2", "Wait2",
         "Done", "Crashed", "Choosing"}

Max(vs) == IF vs = {} THEN Bottom ELSE Max(vs)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ loc = [p \in Proc |-> "Broadcast1"]
    /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]  \* arbitrary prop
    /\ localView = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

Broadcast1(p) ==
    /\ loc[p] = "Broadcast1"
    /\ sent' = sent \cup {[type |-> "Phase1", sender |-> p,
                          value |-> prop[p], est |-> Bottom]}
    /\ loc' = [loc EXCEPT ![p] = "Wait1"]
    /\ UNCHANGED <<localView, prop, est, decision, crashed, recv>>

Receive1(p) ==
    /\ loc[p] = "Wait1"
    /\ \E m \in sent :
        /\ m.type = "Phase1"
        /\ m.sender \notin recv[p]
        /\ localView' = [localView EXCEPT ![p][m.sender] = m.value]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
    /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

ComputeEst(p) ==
    /\ loc[p] = "Wait1"
    /\ Cardinality(recv[p]) >= N - T
    /\ est' = [est EXCEPT ![p] = Max({localView[p][q] : q \in Proc})]
    /\ loc' = [loc EXCEPT ![p] = "Broadcast2"]
    /\ UNCHANGED <<localView, prop, decision, crashed, sent, recv>>

Broadcast2(p) ==
    /\ loc[p] = "Broadcast2"
    /\ sent' = sent \cup {[type |-> "Phase2", sender |-> p,
                          value |-> prop[p], est |-> est[p]}]
    /\ loc' = [loc EXCEPT ![p] = "Wait2"]
    /\ UNCHANGED <<localView, prop, est, decision, crashed, recv>>

Receive2(p) ==
    /\ loc[p] = "Wait2"
    /\ \E m \in sent :
        /\ m.type = "Phase2"
        /\ m.sender \notin recv[p]
        /\ localView' = [localView EXCEPT ![p][m.sender] = m.est]
        /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
    /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

Decide(p) ==
    /\ loc[p] = "Wait2"
    /\ \E v \in Values :
        /\ Cardinality({ m \in sent : m.type = "Phase2" /\ m.est = v }) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<localView, prop, est, crashed, sent, recv>>

MoveToChoosing(p) ==
    /\ loc[p] = "Wait2"
    /\ \A v \in Values :
        Cardinality({ m \in sent : m.type = "Phase2" /\ m.est = v }) < N - T
    /\ Cardinality(recv[p]) = N
    /\ loc' = [loc EXCEPT ![p] = "Choosing"]
    /\ UNCHANGED <<localView, prop, est, decision, crashed, sent, recv>>

Choosing(p) ==
    /\ loc[p] = "Choosing"
    /\ \E v \in Values :
        /\ v \in {localView[p][q] : q \in Proc}
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "Done"]
    /\ UNCHANGED <<localView, prop, est, crashed, sent, recv>>

Crash(p) ==
    /\ loc[p] \notin {"Done", "Crashed"}
    /\ crashed < F
    /\ crashed' = crashed + 1
    /\ loc' = [loc EXCEPT ![p] = "Crashed"]
    /\ UNCHANGED <<localView, prop, est, decision, sent, recv>>

Next ==
    \/ \E p \in Proc : Broadcast1(p)
    \/ \E p \in Proc : Receive1(p)
    \/ \E p \in Proc : ComputeEst(p)
    \/ \E p \in Proc : Broadcast2(p)
    \/ \E p \in Proc : Receive2(p)
    \/ \E p \in Proc : Decide(p)
    \/ \E p \in Proc : MoveToChoosing(p)
    \/ \E p \in Proc : Choosing(p)
    \/ \E p \in Proc : Crash(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<loc, localView, prop, est, decision, crashed, sent, recv>>

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ loc \in [Proc -> Locs]
    /\ prop \in [Proc -> Values]
    /\ est \in [Proc -> (Values \cup {Bottom})]
    /\ decision \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \in Nat
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Proc]

(* ----------------------------------------------------------------------
   Safety properties
   ---------------------------------------------------------------------- *)
Validity ==
    \A p \in Proc :
        decision[p] # Bottom => decision[p] \in Values

Agreement ==
    \A p, q \in Proc :
        /\ decision[p] # Bottom
        /\ decision[q] # Bottom
        => decision[p] = decision[q]

=============================================================================