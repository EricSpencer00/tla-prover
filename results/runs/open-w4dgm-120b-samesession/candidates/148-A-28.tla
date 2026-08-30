---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Signature verification is a set membership check on the public key that
\* corresponds to the private key used to sign the block.
SignatureValid(sig, pk) == sig \in {p \in PrivateKey : PublicKey[p] = pk}

VARIABLES lastHash, ledger, received
vars == <<lastHash, ledger, received>>

\* The per-node ledger copy maps every hash to either a real block or a
\* distinguished sentinel; every node's own received set must drain to empty
\* for the network to quiesce.
EmptyLedger == [h \in Hash |-> NoBlock]

Balance(n, h) ==
  IF h = NoHash THEN 0
  ELSE IF ledger[n][h] = NoBlock THEN Balance(n, NoHash)
  ELSE IF ledger[n][h].type = "send" THEN -ledger[n][h].amount + Balance(n, ledger[n][h].prev)
  ELSE IF ledger[n][h].type = "receive" THEN ledger[n][h].amount + Balance(n, ledger[n][h].prev)
  ELSE Balance(n, ledger[n][h].prev)

RECURSIVE ChainBalance(_)
ChainBalance(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE h \in S : TRUE IN Balance(CHOOSE n \in Node : TRUE, h) + ChainBalance(S \ {h})

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> EmptyLedger]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(p, n) ==
  /\ lastHash = NoHash
  /\ lastHash' = CalculateHash([type |-> "genesis", pk |-> PublicKey[p], amt |-> GenesisBalance, prev |-> NoHash, node |-> n], NoHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "genesis", pk |-> PublicKey[p], amt |-> GenesisBalance, prev |-> NoHash, node |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {[type |-> "genesis", pk |-> PublicKey[p], amt |-> GenesisBalance, prev |-> NoHash, node |-> n]]}

CreateSendBlock(p, n, r, amt) ==
  /\ ledger[n][lastHash] # NoBlock
  /\ Balance(n, lastHash) >= amt
  /\ lastHash' = CalculateHash([type |-> "send", pk |-> PublicKey[p], amt |-> amt, prev |-> lastHash, node |-> n], lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "send", pk |-> PublicKey[p], amt |-> amt, prev |-> lastHash, node |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {[type |-> "send", pk |-> PublicKey[p], amt |-> amt, prev |-> lastHash, node |-> n]]}

CreateOpenBlock(p, n, h) ==
  /\ ledger[n][h] # NoBlock
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].pk = PublicKey[p]
  /\ \A m \in Node : ledger[m][h] # NoBlock => ledger[m][h].node = n
  /\ lastHash' = CalculateHash([type |-> "open", pk |-> PublicKey[p], amt |-> 0, prev |-> h, node |-> n], lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "open", pk |-> PublicKey[p], amt |-> 0, prev |-> h, node |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {[type |-> "open", pk |-> PublicKey[p], amt |-> 0, prev |-> h, node |-> n]]}

CreateReceiveBlock(p, n, h) ==
  /\ ledger[n][h] # NoBlock
  /\ ledger[n][h].type = "send"
  /\ ledger[n][h].pk = PublicKey[p]
  /\ lastHash' = CalculateHash([type |-> "receive", pk |-> PublicKey[p], amt |-> 0, prev |-> lastHash, node |-> n], lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "receive", pk |-> PublicKey[p], amt |-> 0, prev |-> lastHash, node |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {[type |-> "receive", pk |-> PublicKey[p], amt |-> 0, prev |-> lastHash, node |-> n]]]

CreateChangeRepBlock(p, n) ==
  /\ ledger[n][lastHash] # NoBlock
  /\ lastHash' = CalculateHash([type |-> "change", pk |-> PublicKey[p], amt |-> 0, prev |-> lastHash, node |-> n], lastHash)
  /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] = [type |-> "change", pk |-> PublicKey[p], amt |-> 0, prev |-> lastHash, node |-> n]]]
  /\ received' = [m \in Node |-> received[m] \cup {[type |-> "change", pk |-> PublicKey[p], amt |-> 0, prev |-> lastHash, node |-> n]]]

ValidateSend(b, n) ==
  /\ ledger[n][b.prev] # NoBlock
  /\ \A m \in Node : ledger[m][b.prev].node = n
  /\ Balance(n, b.prev) >= b.amt
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![b] = b]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  /\ UNCHANGED <<lastHash>>

ValidateOpen(b, n) ==
  /\ b.amt = 0
  /\ ledger[n][b.prev] # NoBlock
  /\ ledger[n][b.prev].type = "send"
  /\ ledger[n][b.prev].pk = b.pk
  /\ \A m \in Node : ledger[m][b.prev] # NoBlock => ledger[m][b.prev].node = n
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![b] = b]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  /\ UNCHANGED <<lastHash>>

ValidateReceive(b, n) ==
  /\ b.amt = 0
  /\ ledger[n][b.prev] # NoBlock
  /\ \A m \in Node : ledger[m][b.prev].node = n
  /\ \A m \in Node : ledger[m][b.amt] = NoBlock
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![b] = b]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  /\ UNCHANGED <<lastHash>>

ValidateGeneral(b, n) ==
  /\ b.type \in {"open", "receive"} => ValidateOpen(b, n)
  /\ b.type = "send" => ValidateSend(b, n)
  /\ b.type = "receive" => ValidateReceive(b, n)
  /\ UNCHANGED <<lastHash>>

ValidateAny == \E n \in Node, b \in received[n] : ValidateGeneral(b, n)

Next ==
  \/ \E p \in PrivateKey, n \in Node : CreateGenesisBlock(p, n)
  \/ \E p \in PrivateKey, n \in Node, r \in Node, amt \in 1..GenesisBalance : CreateSendBlock(p, n, r, amt)
  \/ \E p \in PrivateKey, n \in Node, h \in Hash : CreateOpenBlock(p, n, h)
  \/ \E p \in PrivateKey, n \in Node, h \in Hash : CreateReceiveBlock(p, n, h)
  \/ \E p \in PrivateKey, n \in Node : CreateChangeRepBlock(p, n)
  \/ ValidateAny

Spec == Init /\ [][Next]_vars /\ WF_vars(ValidateAny)

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> [type : {"genesis", "send", "receive", "open", "change"}, pk : PublicKey, amt : 0..GenesisBalance, prev : Hash \cup {NoHash}, node : Node] \cup {NoBlock}]]
  /\ received \in [Node -> SUBSET [type : {"genesis", "send", "receive", "open", "change"}, pk : PublicKey, amt : 0..GenesisBalance, prev : Hash \cup {NoHash}, node : Node]]


\* A valid signature is exactly what stops a forged block from entering a chain.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlock => SignatureValid(ledger[n][h].pk, PublicKey[CHOOSE k \in PrivateKey : PublicKey[k] = ledger[n][h].pk])

====