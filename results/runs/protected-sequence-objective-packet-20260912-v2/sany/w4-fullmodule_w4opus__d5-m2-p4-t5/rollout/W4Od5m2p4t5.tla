---- MODULE W4Od5m2p4t5 ----
EXTENDS Naturals, FiniteSets

CONSTANTS Capacity, Players, Servers, Admin
VARIABLES lobby, vote, state

TypeOK ==
  /\ lobby \in [Players -> BOOLEAN]
  /\ vote \in [Servers -> BOOLEAN]
  /\ state \in {"idle", "voting", "committed", "aborted"}

Init ==
  /\ lobby = [p \in Players |-> FALSE]
  /\ vote = [s \in Servers |-> FALSE]
  /\ state = "idle"

Next ==
  \/ state = "idle" /\ \E p \in Players : (p \notin lobby /\ lobby' = lobby \cup {[p |-> TRUE]} /\ vote' = [s \in Servers |-> FALSE] /\ state' = "voting")
  \/ state = "idle" /\ \E p \in Players : (p \in lobby /\ lobby' = lobby \cup {[p |-> FALSE]} /\ vote' = [s \in Servers |-> FALSE] /\ state' = "idle")
  \/ state = "idle" /\ Admin = "admin" /\ \E p \in Players : (lobby' = lobby \cup {[p |-> TRUE]} /\ vote' = [s \in Servers |-> FALSE] /\ state' = "idle")
  \/ state = "idle" /\ Admin = "admin" /\ \E p \in Players : (p \in lobby /\ lobby' = lobby \cup {[p |-> FALSE]} /\ vote' = [s \in Servers |-> FALSE] /\ state' = "idle")
  \/ state = "voting" /\ \E s \in Servers : (vote' = vote \cup {[s |-> TRUE]} /\ state' = "voting")
  \/ state = "voting" /\ \E s \in Servers : (vote' = vote \cup {[s |-> FALSE]} /\ state' = "voting")
  \/ state = "voting" /\ \A s \in Servers : vote[s] = TRUE /\ lobby \cap Players \subseteq {p \in Players : lobby[p]} /\ lobby' = lobby /\ vote' = [s \in Servers |-> FALSE] /\ state' = "committed"
  \/ state = "voting" /\ \A s \in Servers : vote[s] = FALSE /\ lobby' = lobby /\ vote' = [s \in Servers |-> FALSE] /\ state' = "aborted"
  \/ state = "committed" /\ lobby \cap Players \subseteq {p \in Players : lobby[p]} /\ lobby' = lobby /\ vote' = [s \in Servers |-> FALSE] /\ state' = "idle"
  \/ state = "aborted" /\ lobby' = lobby /\ vote' = [s \in Servers |-> FALSE] /\ state' = "idle"

CapacityRespected ==
  \A l \in [Players -> BOOLEAN], l \subseteq lobby : Cardinality(l) <= Capacity

====