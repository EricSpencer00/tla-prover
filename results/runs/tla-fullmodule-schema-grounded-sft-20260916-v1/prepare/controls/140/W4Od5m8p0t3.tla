-------------------------- MODULE W4Od5m8p0t3 --------------------------
EXTENDS Naturals

Hosts == {"hostRookery", "hostSpire"}
Brackets == {"bracketBronze", "bracketGold"}
FreeLock == "freeLock"
Nobody == "nobody"
NoBracket == "noBracket"
LadderIdle == [by |-> Nobody, bracket |-> NoBracket]

VARIABLES regionLock, bracketLock, ladderWrite, slowSpell

vars == <<regionLock, bracketLock, ladderWrite, slowSpell>>

TypeOK ==
    /\ regionLock \in Hosts \cup {FreeLock}
    /\ bracketLock \in [Brackets -> Hosts \cup {FreeLock}]
    /\ ladderWrite \in [by : Hosts \cup {Nobody}, bracket : Brackets \cup {NoBracket}]
    /\ slowSpell \subseteq Hosts

Init ==
    /\ regionLock = FreeLock
    /\ bracketLock = [b \in Brackets |-> FreeLock]
    /\ ladderWrite = LadderIdle
    /\ slowSpell = {}

TakeRegionLock(h) ==
    /\ h \notin slowSpell
    /\ regionLock = FreeLock
    /\ regionLock' = h
    /\ UNCHANGED <<bracketLock, ladderWrite, slowSpell>>

TakeBracketLock(h, b) ==
    /\ h \notin slowSpell
    /\ regionLock = h
    /\ bracketLock[b] = FreeLock
    /\ bracketLock' = [bracketLock EXCEPT ![b] = h]
    /\ UNCHANGED <<regionLock, ladderWrite, slowSpell>>

BeginLadderWrite(h, b) ==
    /\ h \notin slowSpell
    /\ regionLock = h
    /\ bracketLock[b] = h
    /\ ladderWrite.by = Nobody
    /\ ladderWrite' = [by |-> h, bracket |-> b]
    /\ UNCHANGED <<regionLock, bracketLock, slowSpell>>

EndLadderWrite(h) ==
    /\ h \notin slowSpell
    /\ ladderWrite.by = h
    /\ ladderWrite' = LadderIdle
    /\ UNCHANGED <<regionLock, bracketLock, slowSpell>>

DropLocks(h) ==
    /\ h \notin slowSpell
    /\ regionLock = h
    /\ ladderWrite.by # h
    /\ regionLock' = FreeLock
    /\ bracketLock' = [b \in Brackets |-> IF bracketLock[b] = h THEN FreeLock ELSE bracketLock[b]]
    /\ UNCHANGED <<ladderWrite, slowSpell>>

FallSlow(h) ==
    /\ h \notin slowSpell
    /\ slowSpell' = slowSpell \cup {h}
    /\ UNCHANGED <<regionLock, bracketLock, ladderWrite>>

ComeBack(h) ==
    /\ h \in slowSpell
    /\ slowSpell' = slowSpell \ {h}
    /\ UNCHANGED <<regionLock, bracketLock, ladderWrite>>

Next ==
    \/ \E h \in Hosts : TakeRegionLock(h) \/ EndLadderWrite(h) \/ DropLocks(h)
                        \/ FallSlow(h) \/ ComeBack(h)
    \/ \E h \in Hosts, b \in Brackets : TakeBracketLock(h, b) \/ BeginLadderWrite(h, b)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ SF_vars(EndLadderWrite("hostRookery"))
    /\ SF_vars(EndLadderWrite("hostSpire"))
    /\ WF_vars(ComeBack("hostRookery"))
    /\ WF_vars(ComeBack("hostSpire"))

WriterHoldsItsBracket ==
    ladderWrite.by # Nobody => bracketLock[ladderWrite.bracket] = ladderWrite.by

WritesAlwaysEnd == (ladderWrite.by # Nobody) ~> (ladderWrite.by = Nobody)
=============================================================================