----------------------------- MODULE W4Od10m7p4t3 -----------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Trains, Cap
ASSUME Cap \in Nat

VARIABLES counter, inRegion, snap, loc
\* counter: shared CAS register holding current occupancy of the bounded track region
\* inRegion: set of trains physically inside the region
\* snap: [Trains -> Nat \cup {-1}] each train last read of counter, or "none"
\* loc: [Trains -> {"out","reading","in"}] control location of each train
vars == <<counter, inRegion, snap, loc>>

TypeOK ==
  /\ counter \in 0..Cap
  /\ inRegion \subseteq Trains
  /\ snap \in [Trains -> (0..Cap) \cup {"none"}]
  /\ loc \in [Trains -> {"out","reading","in"}]

Init ==
  /\ counter = 0
  /\ inRegion = {}
  /\ snap = [t \in Trains |-> "none"]
  /\ loc = [t \in Trains |-> "out"]

\* A train reads the occupancy register, snapshotting the expected value (it may then be slow)
Read(t) ==
  /\ loc[t] = "out"
  /\ snap' = [snap EXCEPT ![t] = counter]
  /\ loc' = [loc EXCEPT ![t] = "reading"]
  /\ UNCHANGED <<counter, inRegion>>

\* Compare-and-swap succeeds only if the register is unchanged since the read and below capacity
CasEnter(t) ==
  /\ loc[t] = "reading"
  /\ snap[t] = counter
  /\ counter < Cap
  /\ counter' = counter + 1
  /\ inRegion' = inRegion \cup {t}
  /\ loc' = [loc EXCEPT ![t] = "in"]
  /\ UNCHANGED snap

\* If another train changed the register first, the CAS fails and the train retreats
CasFail(t) ==
  /\ loc[t] = "reading"
  /\ snap[t] # counter
  /\ loc' = [loc EXCEPT ![t] = "out"]
  /\ UNCHANGED <<counter, inRegion, snap>>

\* A train leaves the region and decrements the shared register
Leave(t) ==
  /\ loc[t] = "in"
  /\ counter' = counter - 1
  /\ inRegion' = inRegion \ {t}
  /\ loc' = [loc EXCEPT ![t] = "out"]
  /\ UNCHANGED snap

Next == \E t \in Trains : Read(t) \/ CasEnter(t) \/ CasFail(t) \/ Leave(t)

Spec == Init /\ [][Next]_vars

\* The bounded track region never holds more trains than its capacity.
CapacityOK == Cardinality(inRegion) <= Cap

=============================================================================