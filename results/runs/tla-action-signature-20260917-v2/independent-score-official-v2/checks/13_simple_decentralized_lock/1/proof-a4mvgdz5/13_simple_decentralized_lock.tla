---- MODULE 13_simple_decentralized_lock ----
\* benchmark: ex-simple-decentralized-lock

EXTENDS TLC, FiniteSetTheorems, TLAPS

CONSTANT Node

VARIABLE message
VARIABLE has_lock

vars == <<message, has_lock>>

Send(src, dst) ==
    /\ src \in has_lock
    /\ message' = message \cup {<<src, dst>>}
    /\ has_lock' = has_lock \ {src}

Recv(src, dst) ==
    /\ <<src, dst>> \in message
    /\ message' = message \ {<<src,dst>>}
    /\ has_lock' = has_lock \cup {dst}

Next ==
    \/ \E src,dst \in Node : Send(src,dst)
    \/ \E src,dst \in Node : Recv(src,dst)

NextUnchanged == UNCHANGED vars

Init ==
    \E start \in Node :
        /\ message = {}
        /\ has_lock = {start}

TypeOK == 
    /\ message \in SUBSET (Node \X Node)
    /\ has_lock \in SUBSET Node

\* Two nodes can't hold lock at once.
Inv == \A x,y \in Node : (x \in has_lock /\ y \in has_lock) => (x = y)

\* Human derived inductive invariant.
IndHuman == 
    /\ TypeOK 
    /\ Inv
    /\ \A n,t \in Node : <<n,t>> \in message => has_lock = {}
    /\ \A a,b \in message : a = b
    
\* Human derived inductive invariant.
IndHumanB ==
    /\ TypeOK 
    /\ Inv
    /\ \A n,t \in Node : <<n,t>> \in message => has_lock = {}
    /\ \A a,b,c,d \in Node : (<<a,b>> \in message /\ <<c,d>> \in message) => (a=c /\ b=d)
    
\* Inductive strengthening conjuncts
Inv531_1_0_def == (has_lock = {}) \/ ((message = {}))
Inv4437_2_1_def == \A VARS \in Node : \A VART \in Node : \A VARU \in Node : \A VARV \in Node : (VARS=VART /\ message=message) \/ (~(<<VARS,VARU>> \in message) \/ (~(<<VART,VARV>> \in message)))
Inv4494_2_2_def == \A VARS \in Node : \A VART \in Node : \A VARU \in Node : (VARS=VART /\ message=message) \/ (~(<<VARU,VARS>> \in message) \/ (~(<<VARU,VART>> \in message)))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv531_1_0_def
  /\ Inv4437_2_1_def
  /\ Inv4494_2_2_def
  
ASSUME NodeFin == IsFiniteSet(Node)

THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY SMT DEF vars, Send, Recv, Next, NextUnchanged, Init, TypeOK, Inv, IndHuman, IndHumanB, Inv531_1_0_def, Inv4437_2_1_def, Inv4494_2_2_def, IndAuto
====