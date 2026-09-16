---- MODULE W4Od2m0p1t1 ----
EXTENDS Integers, FiniteSets

Robots == {"rb1", "rb2"}
Bins   == {"bn1", "bn2"}
MaxVer == 2

VARIABLES rec, inbox, applied, busy

vars == <<rec, inbox, applied, busy>>

Init ==
    /\ rec     = [b \in Bins |-> 0]
    /\ inbox   = {}
    /\ applied = {}
    /\ busy    = [r \in Robots |-> FALSE]

Prepare(r, b) ==
    /\ ~busy[r]
    /\ inbox' = inbox \cup {[bin |-> b, base |-> rec[b], who |-> r]}
    /\ busy'  = [busy EXCEPT ![r] = TRUE]
    /\ UNCHANGED <<rec, applied>>

Apply(m) ==
    /\ m \in inbox
    /\ rec[m.bin] = m.base
    /\ rec[m.bin] < MaxVer
    /\ applied' = applied \cup {[bin |-> m.bin, ver |-> rec[m.bin], src |-> m.who]}
    /\ rec' = [rec EXCEPT ![m.bin] = @ + 1]
    /\ inbox' = inbox \ {m}
    /\ busy'  = [busy EXCEPT ![m.who] = FALSE]

Discard(m) ==
    /\ m \in inbox
    /\ rec[m.bin] # m.base
    /\ inbox' = inbox \ {m}
    /\ busy'  = [busy EXCEPT ![m.who] = FALSE]
    /\ UNCHANGED <<rec, applied>>

ExternalWrite(b) ==
    /\ rec[b] < MaxVer
    /\ applied' = applied \cup {[bin |-> b, ver |-> rec[b], src |-> "ext"]}
    /\ rec' = [rec EXCEPT ![b] = @ + 1]
    /\ UNCHANGED <<inbox, busy>>

Cancel(m) ==
    /\ m \in inbox
    /\ inbox' = inbox \ {m}
    /\ busy'  = [busy EXCEPT ![m.who] = FALSE]
    /\ UNCHANGED <<rec, applied>>

Next ==
    \/ \E r \in Robots, b \in Bins : Prepare(r, b)
    \/ \E m \in inbox : Apply(m)
    \/ \E m \in inbox : Discard(m)
    \/ \E b \in Bins : ExternalWrite(b)
    \/ \E m \in inbox : Cancel(m)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ rec     \in [Bins -> 0..MaxVer]
    /\ inbox   \subseteq [bin : Bins, base : 0..MaxVer, who : Robots]
    /\ applied \subseteq [bin : Bins, ver : 0..MaxVer, src : Robots \cup {"ext"}]
    /\ busy    \in [Robots -> BOOLEAN]

NoLostUpdate ==
    \A b \in Bins : rec[b] = Cardinality({x \in applied : x.bin = b})

====