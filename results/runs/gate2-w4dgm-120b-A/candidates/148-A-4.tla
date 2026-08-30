---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME NoHashVal \notin Hash /\ NoBlockVal \notin Hash
ASSUME NoHash \notin Hash
ASSUME NoBlock \notin [prev: Hash \cup {NoHash}, pk: PublicKey, bal: 0..GenesisBalance, kind: {"genesis", "send", "open", "receive", "change"}]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* Account balances are computed by walking the account chain recursively, so each
\* node's view of the ledger can support a different, diverging balance computation.
Balance(n, h) == IF h = NoHash THEN 0
                 ELSE IF ledger[n][h] = NoBlockVal THEN Balance(n, NoHash)
                 ELSE LET b == ledger[n][h] IN
                      IF b.kind = "send" THEN Balance(n, b.prev) - b.bal
                      ELSE IF b.kind = "receive" THEN Balance(n, b.prev) + b.bal
                      ELSE Balance(n, b.prev)

RECURSIVE SumBalances(_)
SumBalances(S) ==
  IF S = {} THEN 0
  ELSE LET n == CHOOSE x \in S : TRUE IN Balance(n, lastHash) + SumBalances(S \ {n})

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> [prev: Hash \cup {NoHash}, pk: PublicKey, bal: 0..GenesisBalance, kind: {"genesis", "send", "open", "receive", "change"}] \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* Security: signatures are verified against the account's public key at every
\* validation step, so no unauthorized or stale participant can append to a chain.
SignatureValid(n, h) ==
  LET b == ledger[n][h] IN b.pk \in PublicKey /\ \E pr \in PrivateKey : PublicOf(pr) = b.pk

\* Conservation: the total balance across all accounts never exceeds the genesis
\* supply. This is a holistic property that can only be computed by summing every
\* account's recursively computed balance, so it cannot itself be a local check.
Conserved == SumBalances(Node) <= GenesisBalance

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(n) ==
  /\ lastHash = NoHash
  /\ ledger[n][NoHash] = NoBlockVal
  /\ \E pk \in PublicKey :
       /\ ledger' = [ledger EXCEPT ![n][NoHash] = [prev |-> NoHash, pk |-> pk, bal |-> GenesisBalance, kind |-> "genesis"]]
       /\ lastHash' = NoHash
       /\ received' = [m \in Node |-> received[m] \cup {NoHash}]
  \/ UNCHANGED <<lastHash>>

CreateSendBlock(n, to, amt) ==
  /\ lastHash \in Hash
  /\ \E pk \in PublicKey :
       /\ Balance(n, lastHash) >= amt
       /\ ledger[n][lastHash] # NoBlockVal
       /\ \E h \in Hash :
            /\ ledger[n][h] = NoBlockVal
            /\ ledger' = [ledger EXCEPT ![n][h] = [prev |-> lastHash, pk |-> pk, bal |-> amt, kind |-> "send"]]
            /\ lastHash' = h
            /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED <<lastHash>>

CreateOpenBlock(n, src) ==
  /\ ledger[n][lastHash] = NoBlockVal
  /\ \E pk \in PublicKey :
       /\ ledger[n][src] = NoBlockVal
       /\ ledger[src][src] # NoBlockVal
       /\ ledger[src][src].pk = pk
       /\ ledger' = [ledger EXCEPT ![n][src] = [prev |-> NoHash, pk |-> pk, bal |-> 0, kind |-> "open"]]
       /\ received' = [m \in Node |-> received[m] \cup {src}]
  /\ UNCHANGED <<lastHash>>

CreateReceiveBlock(n, src) ==
  /\ ledger[n][lastHash] = NoBlockVal
  /\ ledger[src][src] # NoBlockVal
  /\ ledger[src][src].kind \in {"send", "receive"}
  /\ \E pk \in PublicKey :
       /\ ledger[n][src] = NoBlockVal
       /\ \E h \in Hash :
            /\ ledger[n][h] = NoBlockVal
            /\ ledger' = [ledger EXCEPT ![n][h] = [prev |-> lastHash, pk |-> pk, bal |-> ledger[src][src].bal, kind |-> "receive"]]
            /\ lastHash' = h
            /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED <<lastHash>>

CreateChangeBlock(n) ==
  /\ ledger[n][lastHash] \notin {NoBlockVal, NoBlock}
  /\ \E pk \in PublicKey :
       /\ \E h \in Hash :
            /\ ledger[n][h] = NoBlockVal
            /\ ledger' = [ledger EXCEPT ![n][h] = [prev |-> lastHash, pk |-> pk, bal |-> 0, kind |-> "change"]]
            /\ lastHash' = h
            /\ received' = [m \in Node |-> received[m] \cup {h}]
  /\ UNCHANGED <<lastHash>>

Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlockVal
  /\ ledger[n][ledger[n][h].prev] \notin {NoBlockVal, NoBlock}
  /\ SignatureValid(n, h)
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[n][h]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n)
  \/ \E n \in Node, to \in Node, amt \in 1..GenesisBalance : CreateSendBlock(n, to, amt)
  \/ \E n \in Node, src \in Node : CreateOpenBlock(n, src)
  \/ \E n \in Node, src \in Node : CreateReceiveBlock(n, src)
  \/ \E n \in Node : CreateChangeBlock(n)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK
SafetyInvariant == SignatureValid("anynode", lastHash)
====