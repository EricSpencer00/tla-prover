---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS

SPECIFICATION == "Specification"
INIT == "Init"
NEXT == "Next"
INVARIANTS == "Invariants"
PROPERTIES == "Properties"

Emptyness == { x \in Nat : x < 1 }
NoValue == { x \in Nat : x > 0 }
FullRange == { x \in Nat : x >= 0 }

VARIABLES
  zenonBusy,
  isabelleBusy,
  cvc3Busy,
  yicesBusy,
  veritBusy,
  smtZ3Busy,
  spassBusy,
  ls4Busy

vars == <<
  zenonBusy,
  isabelleBusy,
  cvc3Busy,
  yicesBusy,
  veritBusy,
  smtZ3Busy,
  spassBusy,
  ls4Busy
>>

TypeOK ==
  /\ zenonBusy \in BOOLEAN
  /\ isabelleBusy \in BOOLEAN
  /\ cvc3Busy \in BOOLEAN
  /\ yicesBusy \in BOOLEAN
  /\ veritBusy \in BOOLEAN
  /\ smtZ3Busy \in BOOLEAN
  /\ spassBusy \in BOOLEAN
  /\ ls4Busy \in BOOLEAN

Init ==
  /\ zenonBusy = FALSE
  /\ isabelleBusy = FALSE
  /\ cvc3Busy = FALSE
  /\ yicesBusy = FALSE
  /\ veritBusy = FALSE
  /\ smtZ3Busy = FALSE
  /\ spassBusy = FALSE
  /\ ls4Busy = FALSE

StartZenon == /\ zenonBusy = FALSE /\ zenonBusy' = TRUE /\ UNCHANGED << isabelleBusy, cvc3Busy, yicesBusy, veritBusy, smtZ3Busy, spassBusy, ls4Busy >>
FinishZenon == /\ zenonBusy = TRUE /\ zenonBusy' = FALSE /\ UNCHANGED << isabelleBusy, cvc3Busy, yicesBusy, veritBusy, smtZ3Busy, spassBusy, ls4Busy >>

StartIsabelle == /\ isabelleBusy = FALSE /\ isabelleBusy' = TRUE /\ UNCHANGED << zenonBusy, cvc3Busy, yicesBusy, veritBusy, smtZ3Busy, spassBusy, ls4Busy >>
FinishIsabelle == /\ isabelleBusy = TRUE /\ isabelleBusy' = FALSE /\ UNCHANGED << zenonBusy, cvc3Busy, yicesBusy, veritBusy, smtZ3Busy, spassBusy, ls4Busy >>

StartCVC3 == /\ cvc3Busy = FALSE /\ cvc3Busy' = TRUE /\ UNCHANGED << zenonBusy, isabelleBusy, yicesBusy, veritBusy, smtZ3Busy, spassBusy, ls4Busy >>
FinishCVC3 == /\ cvc3Busy = TRUE /\ cvc3Busy' = FALSE /\ UNCHANGED << zenonBusy, isabelleBusy, yicesBusy, veritBusy, smtZ3Busy, spassBusy, ls4Busy >>

StartYices == /\ yicesBusy = FALSE /\ yicesBusy' = TRUE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, veritBusy, smtZ3Busy, spassBusy, ls4Busy >>
FinishYices == /\ yicesBusy = TRUE /\ yicesBusy' = FALSE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, veritBusy, smtZ3Busy, spassBusy, ls4Busy >>

StartVerit == /\ veritBusy = FALSE /\ veritBusy' = TRUE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, yicesBusy, smtZ3Busy, spassBusy, ls4Busy >>
FinishVerit == /\ veritBusy = TRUE /\ veritBusy' = FALSE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, yicesBusy, smtZ3Busy, spassBusy, ls4Busy >>

StartSMTZ3 == /\ smtZ3Busy = FALSE /\ smtZ3Busy' = TRUE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, yicesBusy, veritBusy, spassBusy, ls4Busy >>
FinishSMTZ3 == /\ smtZ3Busy = TRUE /\ smtZ3Busy' = FALSE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, yicesBusy, veritBusy, spassBusy, ls4Busy >>

StartSPASS == /\ spassBusy = FALSE /\ spassBusy' = TRUE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, yicesBusy, veritBusy, smtZ3Busy, ls4Busy >>
FinishSPASS == /\ spassBusy = TRUE /\ spassBusy' = FALSE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, yicesBusy, veritBusy, smtZ3Busy, ls4Busy >>

StartLS4 == /\ ls4Busy = FALSE /\ ls4Busy' = TRUE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, yicesBusy, veritBusy, smtZ3Busy, spassBusy >>
FinishLS4 == /\ ls4Busy = TRUE /\ ls4Busy' = FALSE /\ UNCHANGED << zenonBusy, isabelleBusy, cvc3Busy, yicesBusy, veritBusy, smtZ3Busy, spassBusy >>

Next ==
  \/ StartZenon \/ FinishZenon
  \/ StartIsabelle \/ FinishIsabelle
  \/ StartCVC3 \/ FinishCVC3
  \/ StartYices \/ FinishYices
  \/ StartVerit \/ FinishVerit
  \/ StartSMTZ3 \/ FinishSMTZ3
  \/ StartSPASS \/ FinishSPASS
  \/ StartLS4 \/ FinishLS4

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(FinishZenon) /\ WF_vars(FinishIsabelle) /\ WF_vars(FinishCVC3)
  /\ WF_vars(FinishYices) /\ WF_vars(FinishVerit) /\ WF_vars(FinishSMTZ3)
  /\ WF_vars(FinishSPASS) /\ WF_vars(FinishLS4)

InvarianceRule == (A \in {0, 1}) => (A = 0 \/ A = 1)
WellFormednessRule ==
  /\ ((\E a \in Nat, b \in Nat : a + b = 2) => TRUE)
  /\ ((\E a \in Nat, b \in Nat : a * b = 2) => TRUE)
StrongFairnessRule ==
  /\ ([]A1) ~> (<>B1)
  /\ ([]A2) ~> (<>B2)
WeakFairnessRule ==
  /\ ([]A1) ~> (<>B1)
  /\ ([]A2) ~> (<>B2)
StepSimulationRule == (a \in Nat /\ b \in Nat /\ a < b) ~> (a + 1 \in Nat /\ b \in Nat)

SetExtensionality == (Emptyness = NoValue) => (Emptyness = NoValue)
NoSetContainsEveryValue == ~((FullRange = NoValue) => (FullRange = NoValue))

====