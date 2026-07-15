---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANTS N, T, F, Values, Bottom

(* Derived constants *)
NProc   == 1..N
MsgIds  == 1..(2 * N)   \* enough identifiers for all messages

(*-----------------------------------------------------------------
  Message type
-----------------------------------------------------------------*)
Message == [type : {"Phase1", "Phase2"},
            sender : NProc,
            value : Values,
            est   : Values \cup {Bottom},
            id    : MsgIds]

(*-----------------------------------------------------------------
  State variables
-----------------------------------------------------------------*)
VARIABLES
    loc,        \* control location of each process
    V,          \* N-by-N matrix of observed values
    propVal,    \* proposed value of each process
    est,        \* estimated value after Phase 1
    dec,        \* decision value (Bottom means undecided)
    crashed,    \* set of crashed processes
    Sent,       \* set of sent messages
    Recvd       \* map: process -> set of received messages

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Locs == {"Broadcast1", "Wait1", "Prepare", "Broadcast2",
         "Wait2", "Decided", "Crashed", "Choosing"}

TypeOK ==
    /\ loc \in [NProc -> Locs]
    /\ V \in [NProc -> [NProc -> (Values \cup {Bottom})]]
    /\ propVal \in [NProc -> Values]
    /\ est \in [NProc -> (Values \cup {Bottom})]
    /\ dec \in [NProc -> (Values \cup {Bottom})]
    /\ crashed \subseteq NProc
    /\ Sent \subseteq Message
    /\ Recvd \in [NProc -> SUBSET Message]
    /\ \A p \in NProc : \A m \in Recvd[p] : m.sender \in NProc
    /\ Cardinality(crashed) <= F
    /\ 2 * T < N
    /\ 0 <= F /\ F <= T /\ N > 0
    /\ Bottom \notin Values

Init ==
    /\ loc = [p \in NProc |-> "Broadcast1"]
    /\ V = [p \in NProc |-> [q \in NProc |-> Bottom]]
    /\ propVal \in [NProc -> Values]   \* chosen nondeterministically
    /\ est = [p \in NProc |-> Bottom]
    /\ dec = [p \in NProc |-> Bottom]
    /\ crashed = {}
    /\ Sent = {}
    /\ Recvd = [p \in NProc |-> {}]

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
Broadcast1 ==
    \E p \in NProc :
        /\ loc[p] = "Broadcast1"
        /\ \E v \in Values :
            /\ propVal[p] = v
            /\ \E mId \in MsgIds :
                /\ Sent' = Sent \cup {[type |-> "Phase1",
                                      sender |-> p,
                                      value |-> v,
                                      est |-> Bottom,
                                      id |-> mId]}
                /\ loc' = [loc EXCEPT ![p] = "Wait1"]
                /\ UNCHANGED <<V, propVal, est, dec, crashed, Recvd>>

Receive1 ==
    \E p \in NProc :
        /\ loc[p] = "Wait1"
        /\ \E m \in Sent :
            /\ m.type = "Phase1"
            /\ m.sender \notin crashed
            /\ m.id \notin { mm.id : mm \in Recvd[p] }
            /\ V' = [V EXCEPT ![p][m.sender] = m.value]
            /\ Recvd' = [Recvd EXCEPT ![p] = Recvd[p] \cup {m}]
            /\ UNCHANGED <<loc, propVal, est, dec, crashed, Sent>>

Prepare ==
    \E p \in NProc :
        /\ loc[p] = "Wait1"
        /\ Cardinality({ q \in NProc : V[p][q] # Bottom }) >= N - T
        /\ est' = [est EXCEPT ![p] = 
                      CHOOSE v \in Values : 
                         \A q \in NProc : 
                            (V[p][q] # Bottom => v >= V[p][q])]
        /\ loc' = [loc EXCEPT ![p] = "Broadcast2"]
        /\ UNCHANGED <<V, propVal, dec, crashed, Sent, Recvd>>

Broadcast2 ==
    \E p \in NProc :
        /\ loc[p] = "Broadcast2"
        /\ \E mId \in MsgIds :
            /\ Sent' = Sent \cup {[type |-> "Phase2",
                                  sender |-> p,
                                  value |-> propVal[p],
                                  est |-> est[p],
                                  id |-> mId]}
            /\ loc' = [loc EXCEPT ![p] = "Wait2"]
            /\ UNCHANGED <<V, propVal, est, dec, crashed, Recvd>>

Receive2 ==
    \E p \in NProc :
        /\ loc[p] = "Wait2"
        /\ \E m \in Sent :
            /\ m.type = "Phase2"
            /\ m.sender \notin crashed
            /\ m.id \notin { mm.id : mm \in Recvd[p] }
            /\ V' = [V EXCEPT ![p][m.sender] = m.value]
            /\ Recvd' = [Recvd EXCEPT ![p] = Recvd[p] \cup {m}]
            /\ UNCHANGED <<loc, propVal, est, dec, crashed, Sent>>

DecideFromEst ==
    \E p \in NProc :
        /\ loc[p] = "Wait2"
        /\ \E v \in Values :
            /\ Cardinality({ m \in Recvd[p] : m.type = "Phase2" /\ m.est = v }) >= N - T
            /\ dec' = [dec EXCEPT ![p] = v]
            /\ loc' = [loc EXCEPT ![p] = "Decided"]
            /\ UNCHANGED <<V, propVal, est, crashed, Sent, Recvd>>

MoveToChoosing ==
    \E p \in NProc :
        /\ loc[p] = "Wait2"
        /\ \A v \in Values :
              Cardinality({ m \in Recvd[p] : m.type = "Phase2" /\ m.est = v }) < N - T
        /\ \A q \in NProc : V[p][q] # Bottom   \* all senders observed
        /\ loc' = [loc EXCEPT ![p] = "Choosing"]
        /\ UNCHANGED <<V, propVal, est, dec, crashed, Sent, Recvd>>

ChooseAndDecide ==
    \E p \in NProc :
        /\ loc[p] = "Choosing"
        /\ \E v \in Values :
            /\ v \in { V[p][q] : q \in NProc }
            /\ dec' = [dec EXCEPT ![p] = v]
            /\ loc' = [loc EXCEPT ![p] = "Decided"]
            /\ UNCHANGED <<V, propVal, est, crashed, Sent, Recvd>>

Crash ==
    \E p \in NProc :
        /\ loc[p] # "Crashed"
        /\ Cardinality(crashed) < F
        /\ crashed' = crashed \cup {p}
        /\ loc' = [loc EXCEPT ![p] = "Crashed"]
        /\ UNCHANGED <<V, propVal, est, dec, Sent, Recvd>>

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
    \/ Broadcast1
    \/ Receive1
    \/ Prepare
    \/ Broadcast2
    \/ Receive2
    \/ DecideFromEst
    \/ MoveToChoosing
    \/ ChooseAndDecide
    \/ Crash

Spec == Init /\ [][Next]_<<loc, V, propVal, est, dec, crashed, Sent, Recvd>>

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
Validity ==
    \A p \in NProc :
        dec[p] # Bottom => dec[p] \in Values

Agreement ==
    \A p, q \in NProc :
        /\ dec[p] # Bottom
        /\ dec[q] # Bottom
        => dec[p] = dec[q]

(*-----------------------------------------------------------------
  Theorems (optional, for readability)
-----------------------------------------------------------------*)
THEOREM Spec => []TypeOK

=============================================================================