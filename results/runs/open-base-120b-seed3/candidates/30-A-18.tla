---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* -----------------------------------------------------------------
\* Derived sets
\* -----------------------------------------------------------------
Proc == 1..N

Locs == {"broadcast1", "wait1", "broadcast2", "wait2",
         "choosing", "done", "crashed"}

Message == [type : {"phase1", "phase2"},
            val  : Values \cup {Bottom},
            sender : Proc,
            est  : Values \cup {Bottom}]

\* -----------------------------------------------------------------
\* State variables
\* -----------------------------------------------------------------
VARIABLES loc, view, prop, est, dec, crashedCount, sent, recv

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
Max(S) == 
  IF S = {} THEN Bottom
  ELSE CHOOSE x \in S : \A y \in S : y <= x

ReceivedFrom(p, mtype) ==
  { m.sender : m \in recv[p] /\ m.type = mtype }

CountEst(p, e) ==
  Cardinality({ m \in recv[p] : m.type = "phase2" /\ m.est = e })

AllPhase2Senders(p) ==
  { m.sender : m \in recv[p] /\ m.type = "phase2" }

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
  /\ loc = [p \in Proc |-> "broadcast1"]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop = [p \in Proc |-> CHOOSE v \in Values : TRUE]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
Broadcast1(p) ==
  /\ loc[p] = "broadcast1"
  /\ sent' = sent \cup {
        [type |-> "phase1",
         val  |-> prop[p],
         sender |-> p,
         est  |-> Bottom]
      }
  /\ loc' = [loc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

Receive1(p, m) ==
  /\ m \in sent
  /\ m.type = "phase1"
  /\ loc[p] = "wait1"
  /\ m.sender \notin ReceivedFrom(p, "phase1")
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ UNCHANGED << loc, prop, est, dec, crashedCount, sent >>

Proceed1(p) ==
  /\ loc[p] = "wait1"
  /\ Cardinality({ s \in Proc : view[p][s] # Bottom }) >= N - T
  /\ est' = [est EXCEPT ![p] = Max({ view[p][s] : s \in Proc })]
  /\ loc' = [loc EXCEPT ![p] = "broadcast2"]
  /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

Broadcast2(p) ==
  /\ loc[p] = "broadcast2"
  /\ sent' = sent \cup {
        [type |-> "phase2",
         val  |-> prop[p],
         sender |-> p,
         est  |-> est[p]]
      }
  /\ loc' = [loc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

Receive2(p, m) ==
  /\ m \in sent
  /\ m.type = "phase2"
  /\ loc[p] = "wait2"
  /\ m.sender \notin AllPhase2Senders(p)
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << loc, view, prop, est, dec, crashedCount, sent >>

Decide(p) ==
  /\ loc[p] = "wait2"
  /\ \E e \in Values :
        CountEst(p, e) >= N - T
  /\ LET e == CHOOSE v \in Values : CountEst(p, v) >= N - T IN
        /\ dec' = [dec EXCEPT ![p] = e]
        /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

MoveToChoosing(p) ==
  /\ loc[p] = "wait2"
  /\ Cardinality(AllPhase2Senders(p)) = N
  /\ \A e \in Values : CountEst(p, e) < N - T
  /\ dec' = [dec EXCEPT ![p] = Max({ view[p][s] : s \in Proc })]
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

ChooseAndDecide(p) ==
  /\ loc[p] = "choosing"
  /\ dec' = [dec EXCEPT ![p] = Max({ view[p][s] : s \in Proc })]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(p) ==
  /\ crashedCount < F
  /\ loc[p] # "crashed"
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

\* -----------------------------------------------------------------
\* Next-state relation
\* -----------------------------------------------------------------
Next ==
  \E p \in Proc :
    \/ Broadcast1(p)
    \/ Receive1(p, m)          \* m quantified inside
    \/ Proceed1(p)
    \/ Broadcast2(p)
    \/ Receive2(p, m)
    \/ Decide(p)
    \/ MoveToChoosing(p)
    \/ ChooseAndDecide(p)
    \/ Crash(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<<loc, view, prop, est, dec,
                     crashedCount, sent, recv>>

\* -----------------------------------------------------------------
\* Type correctness invariant
\* -----------------------------------------------------------------
TypeOK ==
  /\ loc \in [Proc -> Locs]
  /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> Values \cup {Bottom}]
  /\ dec \in [Proc -> Values \cup {Bottom}]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

\* -----------------------------------------------------------------
\* Safety invariants
\* -----------------------------------------------------------------
Validity ==
  \A p \in Proc :
    dec[p] # Bottom =>
      /\ dec[p] \in Values
      /\ \E q \in Proc : prop[q] = dec[p]

Agreement ==
  \A p, q \in Proc :
    /\ dec[p] # Bottom
    /\ dec[q] # Bottom
    => dec[p] = dec[q]

=============================================================================