---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* Correct processes run the protocol; faulty ones may send arbitrary messages.
\* The state is per-process location plus a per-process mailbox of (sender,kind)
\* pairs, plus the set of messages actually emitted by correct processes.
\* The critical property is that no correct process accepts without a real
\* broadcast -- that's the "no-broadcast implies no accept" safety law.

Kinds == {"ECHO"}

VARIABLES correct, faulty, loc, inbox, sent

vars == <<correct, faulty, loc, inbox, sent>>

Locs == {"rcvdINIT", "nosend", "sentECHO", "accepted"}

RECURSIVE Distinct(_)
Distinct(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Distinct(S \ {x})

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty \subseteq 1..N
  /\ loc \in [1..N -> Locs]
  /\ inbox \in [1..N -> SUBSET (1..N \X Kinds)]
  /\ sent \subseteq (1..N) \X Kinds

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ N \in Nat /\ T \in Nat /\ F \in Nat

Init ==
  /\ correct = {1 + i : i \in 0..(N-F-1)}
  /\ faulty = {1 + i : i \in (N-F)..(N-1)}
  /\ \E p \in correct :
       \/ loc = [q \in 1..N |-> IF q = p THEN "rcvdINIT" ELSE "nosend"]
       \/ loc = [q \in 1..N |-> IF q = p THEN "nosend" ELSE "rcvdINIT"]
  /\ inbox = [q \in 1..N |-> {}]
  /\ sent = {}

\* Receives every message a correct sender ever emitted, plus any Byzantine one.
Receive(p) ==
  /\ loc[p] \in {"nosend", "rcvdINIT"}
  /\ inbox' = [inbox EXCEPT ![p] = (sent \cup (faulty \X Kinds)) \ {x \in inbox[p] : x[2] \in Kinds}]
  /\ UNCHANGED <<correct, faulty, loc, sent>>

ActOnBroadcast(p) ==
  /\ loc[p] = "rcvdINIT"
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

ActOnMany(p) ==
  /\ loc[p] = "nosend"
  /\ Distinct({m[1] : m \in inbox[p] \cap (1..N \X {"ECHO"})}) >= N - 2 * T
  /\ Distinct({m[1] : m \in inbox[p] \cap (1..N \X {"ECHO"})}) < (N - T)
  /\ loc' = [loc EXCEPT ![p] = "sentECHO"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

ActOnEnough(p) ==
  /\ loc[p] \in {"nosend", "sentECHO"}
  /\ Distinct({m[1] : m \in inbox[p] \cap (1..N \X {"ECHO"})}) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ sent' = sent \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

ActOnOwn(p) ==
  /\ loc[p] = "sentECHO"
  /\ Distinct({m[1] : m \in inbox[p] \cap (1..N \X {"ECHO"})}) >= (N - T)
  /\ loc' = [loc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<correct, faulty, inbox, sent>>

Next ==
  \/ \E p \in correct : Receive(p) \/ ActOnBroadcast(p) \/ ActOnMany(p) \/ ActOnEnough(p) \/ ActOnOwn(p)
  \/ UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in correct : WF_vars(Receive(p) \/ ActOnBroadcast(p) \/ ActOnMany(p) \/ ActOnEnough(p) \/ ActOnOwn(p))

CorrLtl ==
  (\A p \in correct : loc[p] = "rcvdINIT") ~> (\A p \in correct : loc[p] = "accepted")

RelayLtl ==
  (\E p \in correct : loc[p] = "accepted") ~> (\A p \in correct : loc[p] = "accepted")

UnforgLtl ==
  (\A p \in correct : loc[p] = "nosend") ~> (\A p \in correct : loc[p] # "accepted")

====