---- MODULE TLAPS ----
EXTENDS Naturals, Sequences

CONSTANTS Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4, NoBackend, NoSet, SetOfValues

Operators == {Zenon, Isabelle, CVC3, Yices, VeriT, Z3, SPASS, LS4}

VARIABLES obligations, dispatched, timedOut, atMostOnce, attempts

vars == <<obligations, dispatched, timedOut, atMostOnce, attempts>>

TypeOK ==
  /\ obligations \in Seq(Operators)
  /\ dispatched \in [1..Len(obligations) -> Operators \cup {NoBackend}]
  /\ timedOut \in [1..Len(obligations) -> BOOLEAN]
  /\ atMostOnce \in [Operators -> BOOLEAN]
  /\ attempts \in [Operators -> Nat]

Init ==
  /\ obligations = <<>>
  /\ dispatched = [i \in 1..3 |-> NoBackend]
  /\ timedOut = [i \in 1..3 |-> FALSE]
  /\ atMostOnce = [o \in Operators |-> FALSE]
  /\ attempts = [o \in Operators |-> 0]

Dispatch(o) ==
  /\ ~atMostOnce[o]
  /\ Len(obligations) < 3
  /\ obligations' = Append(obligations, o)
  /\ atMostOnce' = [atMostOnce EXCEPT ![o] = TRUE]
  /\ attempts' = [attempts EXCEPT ![o] = attempts[o] + 1]
  /\ UNCHANGED <<dispatched, timedOut>>

RecordResult(i, r) ==
  /\ i \in 1..Len(obligations)
  /\ dispatched[i] = NoBackend
  /\ dispatched' = [dispatched EXCEPT ![i] = r]
  /\ UNCHANGED <<obligations, timedOut, atMostOnce, attempts>>

ReportTimeout(i) ==
  /\ i \in 1..Len(obligations)
  /\ dispatched[i] = NoBackend
  /\ timedOut' = [timedOut EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<obligations, dispatched, atMostOnce, attempts>>

Next ==
  \/ \E o \in Operators : Dispatch(o)
  \/ \E i \in 1..3 : \E r \in Operators \cup {NoBackend} : RecordResult(i, r)
  \/ \E i \in 1..3 : ReportTimeout(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ SF_vars(\E r \in Operators \cup {NoBackend} : RecordResult(1, r))
  /\ SF_vars(\E r \in Operators \cup {NoBackend} : RecordResult(2, r))
  /\ SF_vars(\E r \in Operators \cup {NoBackend} : RecordResult(3, r))

Extensionality ==
  \A X, Y \in {NoSet, SetOfValues} :
    (\A e \in X : e \in Y) /\ (\A e \in Y : e \in X) => X = Y

NoSetIsUniversal ==
  \A X \in {NoSet, SetOfValues} : X # SetOfValues

Complete ==
  /\ Extensionality
  /\ NoSetIsUniversal

====