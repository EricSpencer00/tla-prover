---- MODULE W4Od15m5p5t3 ----
EXTENDS Naturals, FiniteSets
CONSTANTS Symbols, Makers, Quorum, MaxW
None == 0
VARIABLES priced, done, votes, roundSym, waited
vars == <<priced, done, votes, roundSym, waited>>

TypeOK ==
    ( (priced \in [Symbols -> BOOLEAN])
     /\  (done \in [Symbols -> 0..1])
     /\  (votes \in [Makers -> BOOLEAN])
     /\  (roundSym \in {None} \cup Symbols)
     /\  (waited \in [Makers -> 0..MaxW]))

Init ==
    ( (priced = [s \in Symbols |-> FALSE])
     /\  (done = [s \in Symbols |-> 0])
     /\  (votes = [m \in Makers |-> FALSE])
     /\  (roundSym = None)
     /\  (waited = [m \in Makers |-> 0]))

Open(s) ==
    ( (roundSym = None)
     /\  (~priced[s])
     /\  (roundSym' = s)
     /\  (votes' = [m \in Makers |-> FALSE])
     /\  (UNCHANGED <<priced, done, waited>>))

Vote(m) ==
    ( (roundSym # None)
     /\  (~votes[m])
     /\  (votes' = [votes EXCEPT ![m] = TRUE])
     /\  (UNCHANGED <<priced, done, roundSym, waited>>))

Fix ==
    ( (roundSym # None)
     /\  (Cardinality({m \in Makers : votes[m]}) >= Quorum)
     /\  (~priced[roundSym])
     /\  (priced' = [priced EXCEPT ![roundSym] = TRUE])
     /\  (done' = [done EXCEPT ![roundSym] = 1])
     /\  (roundSym' = None)
     /\  (UNCHANGED <<votes, waited>>))

Cancel ==
    ( (roundSym # None)
     /\  (roundSym' = None)
     /\  (UNCHANGED <<priced, done, votes, waited>>))

Wait(m) ==
    ( (waited' = [waited EXCEPT ![m] = (waited[m] + 1) % (MaxW + 1)])
     /\  (UNCHANGED <<priced, done, votes, roundSym>>))

Next ==
    ( (\E s \in Symbols : Open(s))
     \/  (\E m \in Makers : Vote(m))
     \/  (Fix)
     \/  (Cancel)
     \/  (\E m \in Makers : Wait(m)))

Spec == Init /\ [][Next]_vars

AtMostOnce == \A s \in Symbols : done[s] = (IF priced[s] THEN 1 ELSE 0)
====