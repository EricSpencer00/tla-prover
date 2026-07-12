---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, T, F, Values, Bottom

(* ------------------------------------------------------------------- *)
(* Helper definitions                                               *)

\* All process identifiers
Proc == 1..N

\* All values except the special Bottom value
ValuesExBottom == Values \ {Bottom}

\* View of a process: mapping from each process to a value
View == [p \in Proc |-> Values \cup {Bottom}]

\* A message structure
Msg == [type : {"P1", "P2"},
        val : Values,
        est : Values \cup {Bottom},
        sender : Proc]

\* ------------------------------------------------------------------- *)
(* State variables                                                   *)

VARIABLES
    loc,            \* process control location
    proposed,       \* initially chosen value
    view,           \* local view matrix
    estimate,       \* estimated value after phase 1
    decision,       \* final decided value
    crashedCount,   \* number of crashed processes
    sentMsgs,       \* set of all messages sent so far
    recvMsgs        \* set of all messages each process has received

\* ------------------------------------------------------------------- *)
(* Initial condition                                                 *)

Init ==
    /\ crashedCount = 0
    /\ loc = [p \in Proc |-> "B1"]                \* broadcast phase 1
    /\ proposed = [p \in Proc |-> bottom]
    /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ estimate = [p \in Proc |-> Bottom]
    /\ decision = [p \in Proc |-> Bottom]
    /\ sentMsgs = {}
    /\ recvMsgs = [p \in Proc |-> {}]
    /\ \A p \in Proc:
          \E v \in ValuesExBottom: proposed[p] = v

\* ------------------------------------------------------------------- *)
(* Actions                                                          *)

BroadcastP1(p) ==
    /\ loc[p] = "B1"
    /\ LET m == [type |-> "P1",
                 val  |-> proposed[p],
                 est  |-> Bottom,
                 sender |-> p] IN
       /\ sentMsgs' = sentMsgs \cup {m}
       /\ loc' = [loc EXCEPT ![p] = "W1"]

ReceiveP1(p, m) ==
    /\ m \in sentMsgs
    /\ m.type = "P1"
    /\ loc[p] = "W1"
    /\ recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup {m}]
    /\ view' = [view EXCEPT ![p][m.sender] = m.val]
    /\ UNCHANGED <<loc, proposed, estimate, decision,
                   crashedCount, sentMsgs, loc>>

CheckP1Wait(p) ==
    /\ loc[p] = "W1"
    /\ Cardinality({q \in Proc : [type |-> "P1", sender |-> q] \in sentMsgs}) >= N - T
    /\ LET estVal == Max({view[p][q] : q \in Proc}) IN
       /\ estimate' = [estimate EXCEPT ![p] = estVal]
       /\ loc' = [loc EXCEPT ![p] = "B2"]
    /\ UNCHANGED <<proposed, view, decision, crashedCount, sentMsgs, recvMsgs>>

BroadcastP2(p) ==
    /\ loc[p] = "B2"
    /\ LET m == [type |-> "P2",
                 val  |-> proposed[p],
                 est  |-> estimate[p],
                 sender |-> p] IN
       /\ sentMsgs' = sentMsgs \cup {m}
       /\ loc' = [loc EXCEPT ![p] = "W2"]

ReceiveP2(p, m) ==
    /\ m \in sentMsgs
    /\ m.type = "P2"
    /\ loc[p] = "W2"
    /\ recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup {m}]
    /\ UNCHANGED <<loc, proposed, view, estimate, decision,
                   crashedCount, sentMsgs, view>>

FinishWithEst(p, v) ==
    /\ loc[p] = "W2"
    /\ v \in Values
    /\ Cardinality({m \in recvMsgs[p] :
                    m.type = "P2" /\ m.est = v}) >= N - T
    /\ decision' = [decision EXCEPT ![p] = v]
    /\ loc' = [loc EXCEPT ![p] = "Done"]

Choose(p) ==
    /\ loc[p] = "W2"
    /\ \A m \in recvMsgs[p] : m.type = "P2" => m.est \in Values \cup {Bottom}
    /\ LET chosen ==
           CHOOSE v \in Values :
                \E m \in recvMsgs[p] : m.type = "P2" /\ m.val = v
       IN /\ decision' = [decision EXCEPT ![p] = chosen]
          /\ loc' = [loc EXCEPT ![p] = "Done"]

Crash(p) ==
    /\ p \in Proc
    /\ crashedCount < F
    /\ loc[p] \notin {"Crashed", "Done"}
    /\ loc' = [loc EXCEPT ![p] = "Crashed"]
    /\ crashedCount' = crashedCount + 1
    /\ UNCHANGED <<proposed, view, estimate, decision, sentMsgs, recvMsgs>>

\* ------------------------------------------------------------------- *)
(* Next-state relation                                               *)

Next ==
    \/ \E p \in Proc : BroadcastP1(p)
    \/ \E p \in Proc, m \in sentMsgs : ReceiveP1(p, m)
    \/ \E p \in Proc : CheckP1Wait(p)
    \/ \E p \in Proc : BroadcastP2(p)
    \/ \E p \in Proc, m \in sentMsgs : ReceiveP2(p, m)
    \/ \E p \in Proc, v \in Values :
          FinishWithEst(p, v)
    \/ \E p \in Proc :
          Choose(p)
    \/ \E p \in Proc :
          Crash(p)

\* ------------------------------------------------------------------- *)
(* Specification                                                    *)

Spec ==
    Init /\ [][Next]_<<loc, proposed, view, estimate, decision,
                     crashedCount, sentMsgs, recvMsgs>>

\* ------------------------------------------------------------------- *)
(* Type invariant                                                   *)

TypeOK ==
    /\ IsSubset(Proc, {p \in 1..N})                     \* trivial
    /\ LocVal == {"B1", "W1", "B2", "W2", "Done", "Crashed"}
    /\ \A p \in Proc : loc[p] \in LocVal
    /\ \A p \in Proc : proposed[p] \in Values \cup {Bottom}
    /\ \A p \in Proc : \A q \in Proc : view[p][q] \in Values \cup {Bottom}
    /\ \A p \in Proc : estimate[p] \in Values \cup {Bottom}
    /\ \A p \in Proc : decision[p] \in Values \cup {Bottom}
    /\ crashedCount \in 0..F
    /\ sentMsgs \subseteq Msg
    /\ \A p \in Proc : recvMsgs[p] \subseteq sentMsgs

\* ------------------------------------------------------------------- *)
(* Safety properties                                                *)

Validity ==
    \A p \in Proc :
        (decision[p] \in Values) => decision[p] \in proposed

Agreement ==
    \A p, q \in Proc :
        decision[p] \in Values /\ decision[q] \in Values =>
            decision[p] = decision[q]

\* ------------------------------------------------------------------- *)
(* Safety invariant declaration (required by config)                *)

TempC1 == TRUE

\* ------------------------------------------------------------------- *)
(* THEOREM
    The following holds in all reachable states:                       *)
THEOREM Spec => [] (TypeOK /\ Validity /\ Agreement)

====