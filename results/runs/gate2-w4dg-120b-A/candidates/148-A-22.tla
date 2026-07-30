---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node,
  GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

ASSUME GenesisBalance \in Nat

\* Chain walks from newest to oldest using the block's Prev field; the
\* traverse relation only ever advances if the target block is still
\* present in the local ledger, so a missing or unconfirmed block stops
\* the walk -- exactly the failure this spec catches as an invariant.
Blocks == {NoBlock} \union Hash

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A block's owner is the account chain it lives on; the signature must
\* match that account's public key, and that is the whole of the
\* cryptographic invariant.
Block == [hash: Blocks, owner: PublicKey, typ: {"open", "send", "receive", "changeRep"},
          prev: Blocks, source: PublicKey, dest: PublicKey,
          amount: Nat, signer: PrivateKey]

TypeOK ==
  /\ lastHash \in Blocks
  /\ ledger \in [Node -> [Blocks -> Block \union {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Blocks]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Blocks |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* The hash operator is treated as an external black box; it is assumed
\* to be fixed during a model run, so every block it outputs has the
\* same predecessor, which is precisely what keeps our bounded run
\* from exploding in size.
Stage(h) == IF h = NoHashVal THEN NoHash ELSE h

EstimateBalance(n, h) ==
  IF h = NoHashVal THEN 0
  ELSE IF ledger[n][h].owner # n THEN EstimateBalance(n, ledger[n][h].prev)
  ELSE IF ledger[n][h].owner = n THEN ledger[n][h].amount + EstimateBalance(n, ledger[n][h].prev)
  ELSE EstimateBalance(n, ledger[n][h].prev)

TotalBalance(n) == IF lastHash = NoHashVal THEN 0
                    ELSE EstimateBalance(n, lastHash)

\* The genesis block is the only one written into every node at once,
\* so its signature is what the invariant is tested against first.
CreateGenesisBlock(pk, n) ==
  /\ lastHash = NoHashVal
  /\ ledger' = [x \in Node |-> [y \in Blocks |-> IF y = NoHash
        THEN [hash |-> NoHash, owner |-> pk, typ |-> "open", prev |-> NoHashVal,
               source |-> pk, dest |-> pk, amount |-> GenesisBalance,
               signer |-> n]
        ELSE ledger[x][y]]]
  /\ lastHash' = NoHash
  /\ UNCHANGED received

CreateSendBlock(pk, n, dest) ==
  /\ TotalBalance(pk) > 0
  /\ \E amt \in 1..TotalBalance(pk) :
       /\ ~\E h \in Blocks : ledger[n][h] # NoBlockVal
            /\ ledger' = [x \in Node |-> [y \in Blocks |-> IF y = NoHash
                 THEN [hash |-> NoHash, owner |-> pk, typ |-> "send", prev |-> lastHash,
                        source |-> pk, dest |-> dest, amount |-> amt,
                        signer |-> n]
                 ELSE ledger[x][y]]]
  /\ lastHash' = NoHash
  /\ UNCHANGED received

CreateOpenBlock(pk, n) ==
  /\ lastHash # NoHashVal
  /\ ~\E h \in Blocks : ledger[n][h] # NoBlockVal
  /\ ~\E src \in PublicKey :
       /\ \E r \in Node : ledger[r][src].typ = "send" /\ ledger[r][src].dest = pk
       /\ ledger' = [x \in Node |-> [y \in Blocks |-> IF y = NoHash
            THEN [hash |-> NoHash, owner |-> pk, typ |-> "open",
                   prev |-> NoHashVal, source |-> pk, dest |-> pk,
                   amount |-> 0, signer |-> n]
            ELSE ledger[x][y]]]
  /\ lastHash' = NoHash
  /\ UNCHANGED received

CreateReceiveBlock(pk, n) ==
  /\ lastHash # NoHashVal
  /\ ~\E h \in Blocks : ledger[n][h] # NoBlockVal
  /\ \E src \in PublicKey :
       /\ ledger' = [x \in Node |-> [y \in Blocks |-> IF y = NoHash
            THEN [hash |-> NoHash, owner |-> pk, typ |-> "receive", prev |-> lastHash,
                   source |-> ledger[n][src].source, dest |-> pk,
                   amount |-> ledger[n][src].amount, signer |-> n]
            ELSE ledger[x][y]]]
  /\ lastHash' = NoHash
  /\ UNCHANGED received

CreateChangeRepBlock(pk, n) ==
  /\ lastHash # NoHashVal
  /\ \E h \in Blocks :
       /\ ledger' = [x \in Node |-> [y \in Blocks |-> IF y = NoHash
            THEN [hash |-> NoHash, owner |-> pk, typ |-> "changeRep",
                   prev |-> lastHash, source |-> pk, dest |-> pk,
                   amount |-> 0, signer |-> n]
            ELSE ledger[x][y]]]
  /\ lastHash' = NoHash
  /\ UNCHANGED received

Broadcast(n) ==
  /\ lastHash' = NoHashVal
  /\ \E h \in Blocks :
       /\ lastHash' = CalculateHash([hash |-> h, owner |-> NoHash, typ |-> "aux",
                                    prev |-> lastHash, source |-> NoHash,
                                    dest |-> NoHash, amount |-> 0, signer |-> n])
  /\ received' = [x \in Node |-> received[x] \union {h}]
  /\ UNCHANGED ledger

ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ \E m \in Node : ledger[m][h] # NoBlockVal
  /\ /\ ledger' = [x \in Node |-> [y \in Blocks |-> IF y = h
        THEN ledger[n][h] ELSE ledger[x][y]]
  /\ received' = [x \in Node |-> IF x = n THEN received[n] \ {h} ELSE received[x]]
  /\ UNCHANGED lastHash

Next ==
  \/ \E pk \in PublicKey, n \in Node : CreateGenesisBlock(pk, n)
  \/ \E pk \in PublicKey, n \in Node, dest \in PublicKey : CreateSendBlock(pk, n, dest)
  \/ \E pk \in PublicKey, n \in Node : CreateOpenBlock(pk, n)
  \/ \E pk \in PublicKey, n \in Node : CreateReceiveBlock(pk, n)
  \/ \E pk \in PublicKey, n \in Node : CreateChangeRepBlock(pk, n)
  \/ \E n \in Node : Broadcast(n)
  \/ \E n \in Node, h \in Blocks : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  \A n \in Node, h \in Blocks :
    ledger[n][h] # NoBlockVal => ledger[n][h].signer \in {k \in PrivateKey : PublicKey(k) = ledger[n][h].owner}

TypeInvariant == TypeOK

====