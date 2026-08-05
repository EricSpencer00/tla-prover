---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vote == Ballot \X Value

VARIABLES cast, promised

vars == << cast, promised >>

\* A quorum demonstrates a value safe at ballot b if every lower ballot c
\* already has a quorum voting for that same value or that set of
\* acceptors has been exhausted below c.
Safe == {x \in cast : \A c \in 0..(x[1] - 1) : \E q \in MCQuorum :
  \A y \in q : (y, c) \in cast \/ c < promised[y]} \cup {x \in cast : x[1] = 0}

Init ==
  /\ cast = [a \in MCAcceptor |-> {}]
  /\ promised = [a \in MCAcceptor |-> -1]

\* An acceptor may raise its ballot promise, which prevents it from voting
\* below that ballot again.
RaisePromise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED cast

\* An acceptor votes only if no other value already has a quorum in that
\* ballot, the ballot is above its promise, and the value is safe.
Vote(a, b, v) ==
  /\ b >= promised[a]
  /\ \A x \in cast[a] : x[1] # b
  /\ \A c \in cast : (b, v) \notin c
  /\ \E q \in MCQuorum : \A y \in q : (y, b) \notin cast /\ b >= promised[y]
  /\ cast' = [cast EXCEPT ![a] = @ \cup {<< b, v >>}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot : RaisePromise(a, b)
  \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A ballot never contains votes for two different values.
BallotCoherent == \A b \in MCBallot : (\A x \in cast : x[1] = b => x[2] = v1) \/ (\A x \in cast : x[1] = b => x[2] = v2)

Inv ==
  /\ Safe
  /\ BallotCoherent

\* Any quorum voting for a value is the unique chosen value of the run.
ConsensusSpecBar ==
  \A x \in cast : \A q \in MCQuorum :
    (\A a \in q : x \in cast[a]) => (\A y \in q : y \in cast => (x[2] = y[2]))

\* Permutations of acceptors preserve the algorithm's steps, so this gives
\* a symmetry class for the model-checker's reducer.
MCSymmetry == {p \in [Acceptor -> Acceptor] : \A a \in Acceptor, b \in Acceptor : (p[a] = p[b]) => (a = b)}

====