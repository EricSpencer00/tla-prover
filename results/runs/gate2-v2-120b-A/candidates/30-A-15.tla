---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*--------------------------------------------------------------------
  Constants (to be supplied in the .cfg file)
--------------------------------------------------------------------*)
CONSTANTS
    N,          \* number of processes
    T,          \* maximum number of tolerated faults
    F,          \* actual number of crash faults permitted
    Values,     \* finite totally ordered set of proposal values
    Bottom      \* special value distinct from all Values

(*--------------------------------------------------------------------
  Derived sets and helper definitions
--------------------------------------------------------------------*)
Proc == 1..N

MessageType == {"Phase1", "Phase2"}

(* a phase‑2 message also carries an estimated value *)
Message == [type : MessageType,
            sender : Proc,
            prop  : Values,
            est   : Values \cup {Bottom}]

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES
    loc,        \* [p \in Proc -> current control location]
    view,       \* [p \in Proc -> [q \in Proc -> Values \cup {Bottom}]]
    prop,       \* [p \in Proc -> Values]   (initial proposals)
    est,        \* [p \in Proc -> Values \cup {Bottom}]
    dec,        \* [p \in Proc -> Values \cup {Bottom}]
    crashed,    \* the number of crashed processes
    sent,       \* the set of messages that have been broadcast
    recv        \* [p \in Proc -> SUBSET Message]  (messages received by p)

\*--------------------------------------------------------------------
  Control locations (enumerated for readability)
--------------------------------------------------------------------*)
LocBC1   == "BroadcastPhase1"
LocW1    == "WaitPhase1"
LocBC2   == "BroadcastPhase2"
LocW2    == "WaitPhase2"
LocChoose== "Choosing"
LocDone  == "Done"
LocCrashed=="Crashed"

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ loc   = [p \in Proc |-> LocBC1]
    /\ prop  = [p \in Proc |-> CHOOSE v \in Values : TRUE] \* nondeterministically pick a proposal
    /\ view  = [p \in Proc |-> [q \in Proc |-> Bottom]]
    /\ est   = [p \in Proc |-> Bottom]
    /\ dec   = [p \in Proc |-> Bottom]
    /\ crashed = 0
    /\ sent  = {}
    /\ recv  = [p \in Proc |-> {}]

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

(* 1. Broadcast a Phase‑1 message *)
BC1(p) ==
    /\ loc[p] = LocBC1
    /\ loc'   = [loc EXCEPT ![p] = LocW1]
    /\ sent'  = sent \cup { [type |-> "Phase1",
                            sender |-> p,
                            prop   |-> prop[p],
                            est    |-> Bottom] }
    /\ UNCHANGED <<view, est, dec, crashed, recv>>

(* 2. Receive a Phase‑1 message *)
RCV1(p,m) ==
    /\ loc[p] \in {LocW1, LocW2, LocChoose, LocDone, LocCrashed}
    /\ m \in sent
    /\ m.type = "Phase1"
    /\ view' = [view EXCEPT ![p][m.sender] = m.prop]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

(* 3. After receiving enough Phase‑1 messages, compute estimate and move to Phase‑2 *)
ReadyForBC2(p) ==
    /\ loc[p] = LocW1
    /\ Cardinality({ m \in recv[p] : m.type = "Phase1"}) >= N - T
    /\ loc'  = [loc EXCEPT ![p] = LocBC2]
    /\ est'  = [est EXCEPT ![p] = 
                Max({ view[p][q] : q \in Proc })]
    /\ UNCHANGED <<view, prop, dec, crashed, sent, recv>>

(* 4. Broadcast a Phase‑2 message *)
BC2(p) ==
    /\ loc[p] = LocBC2
    /\ loc'   = [loc EXCEPT ![p] = LocW2]
    /\ sent'  = sent \cup { [type |-> "Phase2",
                            sender |-> p,
                            prop   |-> prop[p],
                            est    |-> est[p]] }
    /\ UNCHANGED <<view, est, dec, crashed, recv>>

(* 5. Receive a Phase‑2 message *)
RCV2(p,m) ==
    /\ loc[p] \in {LocW2, LocChoose, LocDone, LocCrashed}
    /\ m \in sent
    /\ m.type = "Phase2"
    /\ view' = [view EXCEPT ![p][m.sender] = m.est]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
    /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

(* 6. Decide when N‑T messages share the same estimate *)
Decide(p) ==
    /\ loc[p] = LocW2
    /\ \E v \in Values :
        Cardinality({ m \in recv[p] :
                     m.type = "Phase2" /\ m.est = v }) >= N - T
    /\ dec'   = [dec EXCEPT ![p] = v]
    /\ loc'   = [loc EXCEPT ![p] = LocDone]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

(* 7. All Phase‑2 messages received without reaching a threshold -> Choosing *)
Choose(p) ==
    /\ loc[p] = LocW2
    /\ Cardinality({ m \in recv[p] : m.type = "Phase2"}) = N
    /\ \A v \in Values : 
        Cardinality({ m \in recv[p] : m.type = "Phase2" /\ m.est = v }) < N - T
    /\ \E v \in Values :
          Cardinality({ q \in Proc : view[p][q] = v }) > 0
    /\ LET v == CHOOSE w \in Values :
                Cardinality({ q \in Proc : view[p][q] = w }) > 0 IN
       /\ dec' = [dec EXCEPT ![p] = v]
       /\ loc' = [loc EXCEPT ![p] = LocDone]
    /\ UNCHANGED <<view, prop, est, crashed, sent, recv>>

(* 8. A process may crash, provided we stay within the fault bound *)
Crash(p) ==
    /\ crashed < F
    /\ loc[p] \notin {LocCrashed, LocDone}
    /\ crashed' = crashed + 1
    /\ loc'   = [loc EXCEPT ![p] = LocCrashed]
    /\ UNCHANGED <<view, prop, est, dec, sent, recv>>

(*--------------------------------------------------------------------
  Next-state relation (any enabled action of any process)
--------------------------------------------------------------------*)
Next ==
    \E p \in Proc :
        \/ BC1(p)
        \/ \E m \in sent : RCV1(p,m)
        \/ ReadyForBC2(p)
        \/ BC2(p)
        \/ \E m \in sent : RCV2(p,m)
        \/ Decide(p)
        \/ Choose(p)
        \/ Crash(p)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<loc, view, prop, est, dec, crashed, sent, recv>>

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ loc \in [Proc -> {LocBC1, LocW1, LocBC2, LocW2,
                         LocChoose, LocDone, LocCrashed}]
    /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
    /\ prop \in [Proc -> Values]
    /\ est  \in [Proc -> (Values \cup {Bottom})]
    /\ dec  \in [Proc -> (Values \cup {Bottom})]
    /\ crashed \in 0..F
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]

(*--------------------------------------------------------------------
  Safety invariants
--------------------------------------------------------------------*)

(* Validity: every decided value was proposed by some process *)
Validity ==
    \A p \in Proc :
        dec[p] = Bottom \/ 
        \E q \in Proc : prop[q] = dec[p]

(* Agreement: no two non‑bottom decisions differ *)
Agreement ==
    \A p,q \in Proc :
        (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

(*--------------------------------------------------------------------
  Theorem (optional, for TLC)
--------------------------------------------------------------------*)
THEOREM Spec => []Agreement

====