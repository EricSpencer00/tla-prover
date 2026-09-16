---- MODULE W4Od10m6p4t4 ----
EXTENDS Naturals

CONSTANTS Trains, Sections, Horizon, MaxDraw, MaxFeed

VARIABLES grants, clock, feed, drawing

vars == <<grants, clock, feed, drawing>>

Grants == [sec: Sections, train: Trains, amps: 1 .. MaxDraw, until: 1 .. Horizon]

RECURSIVE Amps(_)
Amps(S) ==
    IF S = {} THEN 0
    ELSE LET g == CHOOSE x \in S : TRUE IN g.amps + Amps(S \ {g})

Running(s) == {g \in grants : g.sec = s /\ g.until > clock}
LoadOn(s) == Amps(Running(s))
Booked(t) == \E g \in grants : g.train = t

TypeOK ==
    /\ grants \subseteq Grants
    /\ clock \in 0 .. Horizon
    /\ feed \in [Sections -> 1 .. MaxFeed]
    /\ drawing \subseteq Trains

Init ==
    /\ grants = {}
    /\ clock = 0
    /\ feed = [s \in Sections |-> MaxFeed]
    /\ drawing = {}

\* Traction allowance is let on a lease with an expiry, and the allowance
\* counts against the substation from the moment it is let.
Allow(t, s, a, len) ==
    /\ ~Booked(t)
    /\ clock + len <= Horizon
    /\ LoadOn(s) + a <= feed[s]
    /\ grants' = grants \cup {[sec |-> s, train |-> t, amps |-> a, until |-> clock + len]}
    /\ UNCHANGED <<clock, feed, drawing>>

Notch(t) ==
    /\ t \notin drawing
    /\ \E g \in grants : g.train = t /\ g.until > clock
    /\ drawing' = drawing \cup {t}
    /\ UNCHANGED <<grants, clock, feed>>

Coast(t) ==
    /\ t \in drawing
    /\ drawing' = drawing \ {t}
    /\ UNCHANGED <<grants, clock, feed>>

Tick ==
    /\ clock < Horizon
    /\ clock' = clock + 1
    /\ UNCHANGED <<grants, feed, drawing>>

\* A lapsed allowance is torn up and the train it belonged to comes off power
\* in the same movement.
Lapse(g) ==
    /\ g \in grants
    /\ g.until <= clock
    /\ grants' = grants \ {g}
    /\ drawing' = drawing \ {g.train}
    /\ UNCHANGED <<clock, feed>>

\* The substation is rerated while the railway runs, but never below what its
\* section has already been promised.
Rerate(s, c) ==
    /\ c >= LoadOn(s)
    /\ feed' = [feed EXCEPT ![s] = c]
    /\ UNCHANGED <<grants, clock, drawing>>

NewDay ==
    /\ grants = {}
    /\ clock = Horizon
    /\ clock' = 0
    /\ UNCHANGED <<grants, feed, drawing>>

Ticking == Tick
Lapsing == \E g \in grants : Lapse(g)

Next ==
    \/ \E t \in Trains, s \in Sections, a \in 1 .. MaxDraw, n \in 1 .. Horizon :
           Allow(t, s, a, n)
    \/ \E t \in Trains : Notch(t) \/ Coast(t)
    \/ \E s \in Sections, c \in 1 .. MaxFeed : Rerate(s, c)
    \/ Ticking \/ Lapsing \/ NewDay

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(Ticking) /\ WF_vars(Lapsing)

\* The traction allowances still running on a section never add up to more than
\* what that section's substation can feed.
FeedNeverOversubscribed ==
    \A s \in Sections : LoadOn(s) <= feed[s]

\* Allowances are never held for ever: the register always empties out.
AllowancesLapse == (grants # {}) ~> (grants = {})

====