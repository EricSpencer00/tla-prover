---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase-1 and phase-2 messages carry sender, type, and value; phase 2 also
\* carries the sender's estimated value.
Message == [typ : {"phase1", "phase2"}, val : Values \cup {Bottom},
            est : Values \cup {Bottom}, snd : 0..(N - 1)]

VARIABLES loc, view, proposal, estimate, decided, crashed, msgs, inbox

vars == <<loc, view, proposal, estimate, decided, crashed, msgs, inbox>>

TypeOK ==
  /\ loc \in [0..(N - 1)] ->
        {"broadcast1", "wait1", "prepare", "broadcast2", "wait2", "done", "crashed", "choosing"}
  /\ view \in [0..(N - 1)] -> [0..(N - 1)] -> Values \cup {Bottom}
  /\ proposal \in [0..(N - 1)] -> Values
  /\ estimate \in [0..(N - 1)] -> Values \cup {Bottom}
  /\ decided \in [0..(N - 1)] -> Values \cup {Bottom}
  /\ crashed \in 0..N
  /\ msgs \subseteq Message
  /\ inbox \in [0..(N - 1)] -> SUBSET Message

Init ==
  /\ loc = [p \in 0..(N - 1) |-> "broadcast1"]
  /\ view = [p \in 0..(N - 1) |-> [q \in 0..(N - 1) |-> Bottom]]
  /\ proposal \in [0..(N - 1) -> Values]
  /\ estimate = [p \in 0..(N - 1) |-> Bottom]
  /\ decided = [p \in 0..(N - 1) |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ inbox = [p \in 0..(N - 1) |-> {}]

Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ msgs' = msgs \cup {[typ |-> "phase1", val |-> proposal[p],
                         est |-> Bottom, snd |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED <<view, proposal, estimate, decided, crashed, inbox>>

\* The receiver reads the message according to the phase it is currently in.
Receive(p, m) ==
  /\ loc[p] \in {"wait1", "wait2"}
  /\ m \in msgs
  /\ m.typ = (IF loc[p] = "wait1" THEN "phase1" ELSE "phase2")
  /\ inbox' = [inbox EXCEPT ![p] = inbox[p] \cup {m}]
  /\ msgs' = msgs \ {m}
  /\ UNCHANGED <<loc, view, proposal, estimate, decided, crashed>>

CountSet(S) == Cardinality({m \in S : m.val # Bottom})

\* Phase 1 stalls until the receiver has heard from at least N - T distinct
\* senders, which is the quorum condition.
Prepare(p) ==
  /\ loc[p] = "wait1"
  /\ CountSet({m \in inbox[p] : m.snd # p}) >= (N - T)
  /\ \E q \in 0..(N - 1) : inbox[p] = inbox[p] \cup {[typ |-> "phase1", val |-> view[p][q],
                                                       est |-> Bottom, snd |-> q]}
  /\ view' = [view EXCEPT ![p] = [q \in 0..(N - 1) |-> IF \E m \in inbox[p] : m.snd = q /\ m.val # Bottom
                                                      THEN CHOOSE m \in inbox[p] : m.snd = q /\ m.val # Bottom
                                                                 .val ELSE Bottom];
  /\ estimate' = [estimate EXCEPT ![p] =
                     CHOOSE v \in Values : \A q \in 0..(N - 1) :
                       (view[p][q] # Bottom) => view[p][q] <= v]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ inbox' = [inbox EXCEPT ![p] = {}]
  /\ UNCHANGED <<proposal, decided, crashed, msgs>>

Broadcast2(p) ==
  /\ loc[p] = "broadcast2"
  /\ msgs' = msgs \cup {[typ |-> "phase2", val |-> proposal[p],
                         est |-> estimate[p], snd |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED <<view, proposal, estimate, decided, crashed, inbox>>

Agree(p, v) ==
  /\ loc[p] = "wait2"
  /\ Cardinality({m \in inbox[p] : m.typ = "phase2" /\ m.est = v}) >= (N - T)
  /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, msgs, inbox>>

Choose(p) ==
  /\ loc[p] = "wait2"
  /\ \A q \in 0..(N - 1) : inbox[p] = inbox[p] \cup {[typ |-> "phase2", val |-> view[p][q],
                                                       est |-> Bottom, snd |-> q]}
  /\ \A m \in inbox[p] : m.typ = "phase2"
  /\ Cardinality({m \in inbox[p]}) = N
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ inbox' = [inbox EXCEPT ![p] = {}]
  /\ UNCHANGED <<view, proposal, estimate, decided, crashed, msgs>>

Selecting(p) ==
  /\ loc[p] = "choosing"
  /\ \E q \in 0..(N - 1) : view[p][q] # Bottom
  /\ decided' = [decided EXCEPT ![p] = view[p][CHOOSE q \in 0..(N - 1) : view[p][q] # Bottom]]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, msgs, inbox>>

\* A crash freezes the location and takes nothing more from the process.
Crash(p) ==
  /\ loc[p] # "crashed"
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ inbox' = [inbox EXCEPT ![p] = {}]
  /\ UNCHANGED <<view, proposal, estimate, decided, msgs>>

Next ==
  \/ \E p \in 0..(N - 1) : Broadcast1(p)
  \/ \E p \in 0..(N - 1), m \in Message : Receive(p, m)
  \/ \E p \in 0..(N - 1) : Prepare(p)
  \/ \E p \in 0..(N - 1) : Broadcast2(p)
  \/ \E p \in 0..(N - 1) : Agree(p, proposal[p])
  \/ \E p \in 0..(N - 1) : Choose(p)
  \/ \E p \in 0..(N - 1) : Selecting(p)
  \/ \E p \in 0..(N - 1) : Crash(p)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 0..(N - 1), Broadcast1(p))
  /\ WF_vars(\E p \in 0..(N - 1), Receive(p, [typ |-> "phase1", val |-> Bottom,
                                            est |-> Bottom, snd |-> 0]))
  /\ WF_vars(\E p \in 0..(N - 1), Prepare(p))
  /\ WF_vars(\E p \in 0..(N - 1), Broadcast2(p))
  /\ WF_vars(\E p \in 0..(N - 1), Receive(p, [typ |-> "phase2", val |-> Bottom,
                                            est |-> Bottom, snd |-> 0]))
  /\ WF_vars(\E p \in 0..(N - 1) : Agree(p, proposal[p]))
  /\ WF_vars(\E p \in 0..(N - 1) : Choose(p))
  /\ WF_vars(\E p \in 0..(N - 1) : Selecting(p))

\* The decision is always an originally proposed value; agreement rests on
\* the quorum being larger than the fault tolerance.
Validity == \A p \in 0..(N - 1) : decided[p] # Bottom => \E q \in 0..(N - 1) : proposal[q] = decided[p]
Agreement == \A p, q \in 0..(N - 1) : (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Terminate == <>(\A p \in 0..(N - 1) : loc[p] \in {"crashed", "done"})

\* Condition C1: if enough processes propose the global maximum, quorum
\* voting on the maximum forces every decision to that value.
ConditionalTermination ==
  (\E p \in 0..(N - 1) : proposal[p] = max(Values) >= (F + 1) * Cardinality(Values)) ~> Terminate

====