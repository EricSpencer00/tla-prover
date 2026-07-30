---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

\* Natural-language description: an asynchronous reliable broadcast protocol
\* from Srikanth and Toueg (1987, Fig. 7).  N processes, up to T Byzantine.
\* Two groups: correct processes run the protocol; faulty processes are
\* Byzantine and may emit arbitrary ECHO messages.  InitRecv[p] is the
\* equivalent of p having actually received the broadcaster's INIT.
\* Actions: Receive (a process takes a subset of all sent messages, including
\* Byzantine ones), Immediate (a process that got INIT accepts and ECHOs),
\* Act1 (ECHOs on >= N-2T but < N-T messages), Act2 (ECHOs and accepts on
\* >= N-T messages), Accept (accept on >= N-T messages after ECHOing).  The
\* constant F selects how many processes may be Byzantine; the correct set
\* is chosen nondeterministically at Init, with size N-F.

CONSTANTS N, T, F

Processes == 1..N
Softers == {"INIT"} \cup {<<"ECHO", s>> : s \in Processes}

RECURSIVE Distinct(_, _)
Distinct(S, f) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN 1 + Distinct(S \ {x}, f)

VARIABLES correct, faulty, loc, recv, sent
vars == <<correct, faulty, loc, recv, sent>>

TypeOK ==
  /\ correct \subseteq Processes
  /\ Cardinality(correct) = N - F
  /\ faulty = Processes \ correct
  /\ loc \in [Processes -> {"recv", "none", "sent", "acc"}]
  /\ recv \in [Processes -> SUBSET Softers]
  /\ sent \subseteq Softers

\* every message that has been acted on was sent
FCConstraints == \A p \in Processes : recv[p] \subseteq sent

Init ==
  /\ \E g \in [Processes -> BOOLEAN] :
       /\ Cardinality({p \in Processes : g[p]}) = N - F
       /\ correct = {p \in Processes : g[p]}
  /\ faulty = Processes \ correct
  /\ loc = [p \in Processes |-> IF g[p] THEN "recv" ELSE "none"]
  /\ recv = [p \in Processes |-> {}]
  /\ sent = {}

\* receive any subset of what correct processes sent, plus any Byzantine msgs
Receive(p) ==
  /\ p \in correct
  /\ \E S \subseteq (sent \cup {<<"ECHO", s>> : s \in Processes}):
       recv' = [recv EXCEPT ![p] = recv[p] \cup S]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

Immediate(p) ==
  /\ p \in correct
  /\ loc[p] = "recv"
  /\ loc' = [loc EXCEPT ![p] = "acc"]
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ UNCHANGED <<correct, faulty, recv>>

Act1(p) ==
  /\ p \in correct
  /\ loc[p] = "none"
  /\ Distinct(recv[p], "snd") >= N - 2 * T /\ Distinct(recv[p], "snd") < N - T
  /\ loc' = [loc EXCEPT ![p] = "sent"]
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ UNCHANGED <<correct, faulty, recv>>

Act2(p) ==
  /\ p \in correct
  /\ loc[p] = "none"
  /\ Distinct(recv[p], "snd") >= N - T
  /\ loc' = [loc EXCEPT ![p] = "acc"]
  /\ sent' = sent \cup {<<"ECHO", p>>}
  /\ UNCHANGED <<correct, faulty, recv>>

Accept(p) ==
  /\ p \in correct
  /\ loc[p] = "sent"
  /\ Distinct(recv[p], "snd") >= N - T
  /\ loc' = [loc EXCEPT ![p] = "acc"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E p \in Processes : Receive(p) \/ Immediate(p) \/ Act1(p) \/ Act2(p) \/ Accept(p)

\* No broadcast: no correct process got the INIT message at all.
AllNone == \A p \in correct : loc[p] = "none"

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Processes : Receive(p))
  /\ WF_vars(\E p \in Processes : Immediate(p))
  /\ WF_vars(\E p \in Processes : Act1(p))
  /\ WF_vars(\E p \in Processes : Act2(p))
  /\ WF_vars(\E p \in Processes : Accept(p))

UnforgLtl == AllNone ~> (\A p \in correct : loc[p] = "acc")
CorrLtl == (\A p \in correct : loc[p] = "recv") ~> (\A p \in correct : loc[p] = "acc")
RelayLtl == (\E p \in correct : loc[p] = "acc") ~> (\A p \in correct : loc[p] = "acc")

====