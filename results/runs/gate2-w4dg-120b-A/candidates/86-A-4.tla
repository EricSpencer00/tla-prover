---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

Spec == "BackendPragmas"

MAXTO == 3
MAXLEN == 2

ASSUME Zenon = "Zenon"
ASSUME Isabelle = "Isabelle"
ASSUME CVC3 = "CVC3"
ASSUME Yices = "Yices"
ASSUME veriT = "veriT"
ASSUME Z3 = "Z3"
ASSUME SPASS = "SPASS"
ASSUME LS4 = "LS4"

InitState == "init"
ProveBy(prover) == "proveBy" @@ prover
SetTimeout(dur) == "setTimeout(" @@ dur @@ ")"
CloseGoal == "closeGoal"

IsaAutomated == ProveBy(Isabelle) \X {InitState, "inv"}
ZenonAutomated == ProveBy(Zenon) \X {InitState, "step"}
SmtCooperate == ProveBy(Z3) \X {InitState, "inv"}
YicesCooperate == ProveBy(Yices) \X {InitState, "step"}
VeriTCooperate == ProveBy(veriT) \X {InitState, "step"}
SpassCooperate == ProveBy(SPASS) \X {InitState, "step"}
Cvc3Cooperate == ProveBy(CVC3) \X {InitState, "step"}
PreemptiveFinish == CloseGoal \X {InitState}
Ls4ProveInv == ProveBy(LS4) \X {InitState, "inv"}
Ls4ProveStep == ProveBy(LS4) \X {InitState, "step"}

INIT == TRUE

Next == TRUE

TypeOK ==
    /\ Zenon \in STRING
    /\ Isabelle \in STRING
    /\ CVC3 \in STRING
    /\ Yices \in STRING
    /\ veriT \in STRING
    /\ Z3 \in STRING
    /\ SPASS \in STRING
    /\ LS4 \in STRING

SetBound == TRUE

SpecRewind == TRUE

SpecDone == TRUE

Extensionality ==
    \A A, B \in SUBSET 1..2 : (\A x \in 1..2 : (x \in A) <=> (x \in B)) => (A = B)

CantContainAll ==
    \A A \in SUBSET 1..2 : (A # 1..2) => TRUE

====