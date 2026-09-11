---- MODULE W4Od10m2p0t3 ----
EXTENDS Naturals

CONSTANTS Trains, Interlockings

VARIABLES holders, phase, candidate, prepared
vars == <<holders, phase, candidate, prepared>>

Init ==
    ( (holders = {})
     /\  (phase = "idle")
     /\  (candidate = "none")
     /\  (prepared = {}))

Request(t) ==
    ( (phase = "idle")
     /\  (holders = {})
     /\  (phase' = "voting")
     /\  (candidate' = t)
     /\  (prepared' = {})
     /\  (UNCHANGED holders))

Prepare(i) ==
    ( (phase = "voting")
     /\  (i \in Interlockings)
     /\  (i \notin prepared)
     /\  (prepared' = prepared \cup {i})
     /\  (UNCHANGED <<holders, phase, candidate>>))

Commit ==
    ( (phase = "voting")
     /\  (prepared = Interlockings)
     /\  (holders' = {candidate})
     /\  (phase' = "idle")
     /\  (UNCHANGED <<candidate, prepared>>))

Abort ==
    ( (phase = "voting")
     /\  (phase' = "idle")
     /\  (UNCHANGED <<holders, candidate, prepared>>))

Release(t) ==
    ( (t \in holders)
     /\  (holders' = holders \ {t})
     /\  (UNCHANGED <<phase, candidate, prepared>>))

Next ==
    ( (\E t \in Trains : Request(t))
     \/  (\E i \in Interlockings : Prepare(i))
     \/  (Commit)
     \/  (Abort)
     \/  (\E t \in Trains : Release(t)))

Spec == Init /\ [][Next]_vars

BlockExclusive == holders = {} \/ \E t \in Trains : holders = {t}
====