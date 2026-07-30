---- MODULE TLAPS ----
EXTENDS Naturals

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4

VARIABLES
  zenonCalls, isabelleCalls, cvc3Calls, yicesCalls, veriTCalls, z3Calls, spassCalls, ls4Calls, startTime

vars == << zenonCalls, isabelleCalls, cvc3Calls, yicesCalls, veriTCalls, z3Calls, spassCalls, ls4Calls, startTime >>

MaxCalls == 3
MaxDuration == 10

Init ==
  /\ zenonCalls = 0
  /\ isabelleCalls = 0
  /\ cvc3Calls = 0
  /\ yicesCalls = 0
  /\ veriTCalls = 0
  /\ z3Calls = 0
  /\ spassCalls = 0
  /\ ls4Calls = 0
  /\ startTime = 0

DispatchZenon ==
  /\ zenonCalls < MaxCalls
  /\ zenonCalls' = zenonCalls + 1
  /\ UNCHANGED << isabelleCalls, cvc3Calls, yicesCalls, veriTCalls, z3Calls, spassCalls, ls4Calls, startTime >>

DispatchIsabelle ==
  /\ isabelleCalls < MaxCalls
  /\ isabelleCalls' = isabelleCalls + 1
  /\ UNCHANGED << zenonCalls, cvc3Calls, yicesCalls, veriTCalls, z3Calls, spassCalls, ls4Calls, startTime >>

DispatchCVC3 ==
  /\ cvc3Calls < MaxCalls
  /\ cvc3Calls' = cvc3Calls + 1
  /\ UNCHANGED << zenonCalls, isabelleCalls, yicesCalls, veriTCalls, z3Calls, spassCalls, ls4Calls, startTime >>

DispatchYices ==
  /\ yicesCalls < MaxCalls
  /\ yicesCalls' = yicesCalls + 1
  /\ UNCHANGED << zenonCalls, isabelleCalls, cvc3Calls, veriTCalls, z3Calls, spassCalls, ls4Calls, startTime >>

DispatchVeriT ==
  /\ veriTCalls < MaxCalls
  /\ veriTCalls' = veriTCalls + 1
  /\ UNCHANGED << zenonCalls, isabelleCalls, cvc3Calls, yicesCalls, z3Calls, spassCalls, ls4Calls, startTime >>

DispatchZ3 ==
  /\ z3Calls < MaxCalls
  /\ z3Calls' = z3Calls + 1
  /\ UNCHANGED << zenonCalls, isabelleCalls, cvc3Calls, yicesCalls, veriTCalls, spassCalls, ls4Calls, startTime >>

DispatchSPASS ==
  /\ spassCalls < MaxCalls
  /\ spassCalls' = spassCalls + 1
  /\ UNCHANGED << zenonCalls, isabelleCalls, cvc3Calls, yicesCalls, veriTCalls, z3Calls, ls4Calls, startTime >>

DispatchLS4 ==
  /\ ls4Calls < MaxCalls
  /\ ls4Calls' = ls4Calls + 1
  /\ UNCHANGED << zenonCalls, isabelleCalls, cvc3Calls, yicesCalls, veriTCalls, z3Calls, spassCalls, startTime >>

Tick ==
  /\ startTime < MaxDuration
  /\ startTime' = startTime + 1
  /\ UNCHANGED << zenonCalls, isabelleCalls, cvc3Calls, yicesCalls, veriTCalls, z3Calls, spassCalls, ls4Calls >>

Next ==
  \/ DispatchZenon \/ DispatchIsabelle \/ DispatchCVC3 \/ DispatchYices
  \/ DispatchVeriT \/ DispatchZ3 \/ DispatchSPASS \/ DispatchLS4
  \/ Tick

Spec == Init /\ [][Next]_vars

SetExtensionality == \A X, Y \in SUBSET Nat : (\A e \in Nat : e \in X <=> e \in Y) => X = Y
NoSetContainsAllValues == \A X \in SUBSET Nat : \A e \in Nat : e \notin X

Invariants == SetExtensionality

Properties == NoSetContainsAllValues

====