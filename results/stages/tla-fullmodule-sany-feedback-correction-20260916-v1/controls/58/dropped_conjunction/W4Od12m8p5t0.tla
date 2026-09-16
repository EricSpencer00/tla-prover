---------------------------- MODULE W4Od12m8p5t0 ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Workers, Units, FridgeA, FridgeB, NONE

ASSUME FridgeA \cap FridgeB = {} /\ FridgeA \cup FridgeB = Units

Fridges == {"A", "B"}

FridgeOf(u) == IF u \in FridgeA THEN "A" ELSE "B"

VARIABLES coarse, fine, log, crashed

vars == <<coarse, fine, log, crashed>>

Logged == {log[i] : i \in DOMAIN log}

TypeOK ==
  /\ coarse \in [Fridges -> Workers \cup {NONE}]
    fine \in [Units -> Workers \cup {NONE}]
  /\ log \in Seq(Units)
  /\ crashed \subseteq Workers

Init ==
  /\ coarse = [f \in Fridges |-> NONE]
  /\ fine = [u \in Units |-> NONE]
  /\ log = << >>
  /\ crashed = {}

AcquireCoarse(w, f) ==
  /\ w \notin crashed
  /\ coarse[f] = NONE
  /\ coarse' = [coarse EXCEPT ![f] = w]
  /\ UNCHANGED <<fine, log, crashed>>

AcquireFine(w, u) ==
  /\ w \notin crashed
  /\ coarse[FridgeOf(u)] = w
  /\ fine[u] = NONE
  /\ fine' = [fine EXCEPT ![u] = w]
  /\ UNCHANGED <<coarse, log, crashed>>

Dispatch(w, u) ==
  /\ w \notin crashed
  /\ coarse[FridgeOf(u)] = w
  /\ fine[u] = w
  /\ u \notin Logged
  /\ log' = Append(log, u)
  /\ fine' = [fine EXCEPT ![u] = NONE]
  /\ UNCHANGED <<coarse, crashed>>

ReleaseFine(w, u) ==
  /\ fine[u] = w
  /\ fine' = [fine EXCEPT ![u] = NONE]
  /\ UNCHANGED <<coarse, log, crashed>>

ReleaseCoarse(w, f) ==
  /\ coarse[f] = w
  /\ coarse' = [coarse EXCEPT ![f] = NONE]
  /\ UNCHANGED <<fine, log, crashed>>

Crash(w) ==
  /\ w \notin crashed
  /\ crashed' = crashed \cup {w}
  /\ coarse' = [f \in Fridges |-> IF coarse[f] = w THEN NONE ELSE coarse[f]]
  /\ fine' = [u \in Units |-> IF fine[u] = w THEN NONE ELSE fine[u]]
  /\ UNCHANGED log

Idle == UNCHANGED vars

Next ==
  \/ \E w \in Workers, f \in Fridges : AcquireCoarse(w, f)
  \/ \E w \in Workers, u \in Units : AcquireFine(w, u)
  \/ \E w \in Workers, u \in Units : Dispatch(w, u)
  \/ \E w \in Workers, u \in Units : ReleaseFine(w, u)
  \/ \E w \in Workers, f \in Fridges : ReleaseCoarse(w, f)
  \/ \E w \in Workers : Crash(w)
  \/ Idle

Spec == Init /\ [][Next]_vars

EachUnitDispatchedOnce ==
  \A i, j \in DOMAIN log : log[i] = log[j] => i = j

=============================================================================