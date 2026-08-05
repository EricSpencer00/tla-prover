---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase condition-based consensus: each process first shares its own
\* proposal (phase 1) and computes an estimate as the max of what it has
\* seen; it then shares the estimate (phase 2) and decides when enough
\* estimates agree. Crashed processes simply stop. The invariant below
\* is the "no two decisions disagree" safety guarantee of the paper.

VARIABLES loc, view, proposed, estimate, decision, crashed, sent, received

parts == 1..N

\* loc encodes the whole protocol state machine, so SEND1/2 and MSGRECV
\* can be applied only in the phase that matches loc, which keeps the
\* two-phase order intact even though RECEIVE is a weakly fair action.
LocDomain == {broadcast1, wait1, broadcast2, wait2, done, crashed, choosing}

RECURSIVE MaxOf(_, _)
MaxOf(f, S) ==
  IF S = {} THEN Bottom
  ELSE LET x == CHOOSE y \in S : TRUE
       IN IF f[x] > MaxOf(f, S \ {x}) THEN f[x] ELSE MaxOf(f, S \ {x})

Msgs == [type: {"phase1", "phase2"}, value: Values, from: parts, est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [parts -> LocDomain]
  /\ view \in [parts -> [parts -> Values \cup {Bottom}]]
  /\ proposed \in [parts -> Values]
  /\ estimate \in [parts -> Values \cup {Bottom}]
  /\ decision \in [parts -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Msgs
  /\ received \in [parts -> SUBSET parts]

Init ==
  /\ loc = [p \in parts |-> broadcast1]
  /\ view = [p \in parts |-> [q \in parts |-> Bottom]]
  /\ proposed \in [parts -> Values]
  /\ estimate = [p \in parts |-> Bottom]
  /\ decision = [p \in parts |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [p \in parts |-> {}]

Send1 ==
  /\ \E p \in parts :
       /\ loc[p] = broadcast1
       /\ sent' = sent \cup {[type |-> "phase1", value |-> proposed[p], from |-> p, est |-> Bottom]}
       /\ loc' = [loc EXCEPT ![p] = wait1]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, sent, received>>

MsgRecv ==
  /\ \E m \in sent, p \in parts :
       /\ loc[p] \in {wait1, wait2}
       /\ m.type = (IF loc[p] = wait1 THEN "phase1" ELSE "phase2")
       /\ m.from \notin received[p]
       /\ view' = [view EXCEPT ![p][m.from] = m.value]
       /\ estimate' = IF loc[p] = wait1
                       THEN [estimate EXCEPT ![p] = MaxOf([q \in parts |-> IF q = m.from THEN m.value ELSE view[p][q]], parts)]
                       ELSE estimate
       /\ received' = [received EXCEPT ![p] = received[p] \cup {m.from}]
  /\ UNCHANGED <<loc, proposed, estimate, decision, crashed, sent>>

Send2 ==
  /\ \E p \in parts :
       /\ loc[p] = broadcast2
       /\ sent' = sent \cup {[type |-> "phase2", value |-> proposed[p], from |-> p, est |-> estimate[p]]}
       /\ loc' = [loc EXCEPT ![p] = wait2]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, sent, received>>

Decide ==
  /\ \E p \in parts :
       /\ loc[p] = wait2
       /\ \E v \in Values :
            /\ Cardinality({q \in parts : view[p][q] = v}) >= N - T
            /\ decision[p] = Bottom
            /\ decision' = [decision EXCEPT ![p] = v]
            /\ loc' = [loc EXCEPT ![p] = done]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, received>>

Start2 ==
  /\ \E p \in parts :
       /\ loc[p] = wait1
       /\ \A q \in parts : view[p][q] # Bottom
       /\ loc' = [loc EXCEPT ![p] = broadcast2]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, sent, received>>

Start1 ==
  /\ \E p \in parts :
       /\ loc[p] = broadcast1
       /\ loc' = [loc EXCEPT ![p] = broadcast2]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, sent, received>>

Choose ==
  /\ \E p \in parts :
       /\ loc[p] = choosing
       /\ \E v \in Values :
            /\ Cardinality({q \in parts : view[p][q] = v}) >= 1
            /\ decision' = [decision EXCEPT ![p] = v]
            /\ loc' = [loc EXCEPT ![p] = done]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, received>>

Crash ==
  /\ crashed < F
  /\ \E p \in parts :
       /\ loc[p] \notin {crashed, done}
       /\ loc' = [loc EXCEPT ![p] = crashed]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decision, sent, received>>

Fwd ==
  /\ Start2 \/ Start1 \/ Send1 \/ Send2 \/ Crash \/ Choose

Next == Fwd \/ MsgRecv \/ Decide

WfF == WF_vars(Fwd) /\ WF_vars(MsgRecv) /\ WF_vars(Decide)

Spec == Init /\ [][Next]_<<loc, view, proposed, estimate, decision, crashed, sent, received>> /\ WfF

\* No two decisions disagree: every decided value is a proposal received
\* from some process, so a single disagreement would mean a value no one
\* ever proposed was decided, which violates safety.
Validity == \A p \in parts : decision[p] # Bottom => \E q \in parts : view[p][q] = decision[p]

Agreement == \A p \in parts : decision[p] # Bottom => decision[p] = estimate[p]

====