---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLE pc, flag, ticket, unchecked, nxt, previous

\* Finite version of the natural numbers used for model checking
NatOverride == 0..MaxNat

\* Instance of the original Boulanger specification with all required substitutions
INSTANCE Boulanger AS B WITH
    num      <- N,
    max      <- MaxNat,
    pc       <- pc,
    flag     <- flag,
    ticket   <- ticket,
    unchecked<- unchecked,
    nxt      <- nxt,
    previous <- previous

\* State constraint: ticket numbers must stay strictly below MaxNat
StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

\* Specification (inherits Boulanger's behavior, adding the state constraint)
Spec == B!Spec /\ StateConstraint

\* Inherited invariants
MutualExclusion == B!MutualExclusion
TypeOK           == B!TypeOK
Inv              == B!Inv
====