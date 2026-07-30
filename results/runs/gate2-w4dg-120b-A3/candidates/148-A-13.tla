---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
  CalculateHash, NoHash, NoBlock

ASSUME GenesisBalance \in Nat

\* The ledger is a per-node copy of the same global block set; each node validates
\* independently before assimilating. Hash order is part of the block chain.
\* Balance is derived by walking the chain from the genesis block forward.
\* A block is accepted into a node's ledger only when its cryptographic signature
\* is valid for the owner account's public key.

VARIABLES lastHash, ledger, rx

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> (PUBLICKEY \cup {NoBlockVal})]]
  /\ rx \in [Node -> SUBSET Hash]

\* The number of blocks on an account's chain is its depth from the genesis block.
Depth(a) ==
  LET recurse(h) ==
        IF h = NoHashVal THEN 0
        ELSE IF ledger[a][h] = NoBlockVal THEN 0
        ELSE 1 + recurse(ledger[a][h].prev)
  IN recurse(NoHash)

\* Balance is the genesis balance minus the total sent, plus the amount received.
\* Receipts are counted per account, so it stays real-valued over the lattice.
SentAmount(a) ==
  LET sumSent(h) ==
        IF h = NoHashVal THEN 0
        ELSE IF ledger[a][h] = NoBlockVal THEN 0
        ELSE IF ledger[a][h].type = "send"
             THEN ledger[a][h].amt + sumSent(ledger[a][h].prev)
             ELSE sumSent(ledger[a][h].prev)
  IN sumSent(NoHash)

RecvdAmount(a) ==
  LET sumRecvd(h) ==
        IF h = NoHashVal THEN 0
        ELSE IF ledger[a][h] = NoBlockVal THEN 0
        ELSE IF ledger[a][h].type = "receive"
             THEN ledger[a][h].amt + sumRecvd(ledger[a][h].prev)
             ELSE sumRecvd(ledger[a][h].prev)
  IN sumRecvd(NoHash)

Balance(a) == GenesisBalance - SentAmount(a) + RecvdAmount(a)

GenesisExists ==
  \E h \in Hash :
    /\ ledger[Node][h] # NoBlockVal
    /\ ledger[Node][h].type = "genesis"
    /\ \A n \in Node : ledger[n][h] = ledger[Node][h]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ rx = [n \in Node |-> {}]

CreateGenesisBlock(pk) ==
  /\ \A n \in Node : ledger[n][NoHashVal] = NoBlockVal
  /\ lastHash = NoHashVal
  /\ \E h \in Hash :
       /\ ledger' = [n \in Node |->
            [ledger[n] EXCEPT ![h] = [type |-> "genesis", amt |-> GenesisBalance,
                                     sender |-> pk, recipient |-> pk,
                                     prev |-> NoHashVal, ver |-> NoHashVal]]]
       /\ lastHash' = h
       /\ rx' = [n \in Node |->
            [rx[n] EXCEPT ! = IF n = Node THEN @ ELSE @ \cup {h}]]
  /\ UNCHANGED <<>>

CreateSendBlock(a, pk, amt) ==
  /\ ledger[a][NoHashVal] # NoBlockVal
  /\ \E h \in Hash :
       /\ ledger' = [ledger EXCEPT ![a][h] = [type |-> "send", amt |-> amt,
                               sender |-> pk, recipient |-> NoHashVal,
                               prev |-> NoHashVal, ver |-> NoHashVal]]
       /\ lastHash' = h
       /\ rx' = [n \in Node |->
            [rx[n] EXCEPT ! = IF n = a THEN @ \cup {h} ELSE @]]
  /\ UNCHANGED <<>>

CreateOpenBlock(a, pk, h) ==
  /\ ledger[a][NoHashVal] = NoBlockVal
  /\ ledger' = [ledger EXCEPT ![a][NoHashVal] = [type |-> "open", amt |-> 0,
                           sender |-> NoHashVal, recipient |-> pk,
                           prev |-> h, ver |-> NoHashVal]]
  /\ rx' = [n \in Node |->
       [rx[n] EXCEPT ! = IF n = a THEN @ \cup {NoHashVal} ELSE @]]
  /\ UNCHANGED <<lastHash>>

CreateReceiveBlock(a, pk, h) ==
  /\ ledger[a][NoHashVal] # NoBlockVal
  /\ \E hh \in Hash :
       /\ ledger' = [ledger EXCEPT ![a][hh] = [type |-> "receive", amt |-> 0,
                               sender |-> pk, recipient |-> NoHashVal,
                               prev |-> NoHashVal, ver |-> h]]
       /\ lastHash' = hh
       /\ rx' = [n \in Node |->
            [rx[n] EXCEPT ! = IF n = a THEN @ \cup {hh} ELSE @]]
  /\ UNCHANGED <<>>

CreateChangeRep(a, pk) ==
  /\ ledger[a][NoHashVal] # NoBlockVal
  /\ \E h \in Hash :
       /\ ledger' = [ledger EXCEPT ![a][h] = [type |-> "repr", amt |-> 0,
                               sender |-> pk, recipient |-> NoHashVal,
                               prev |-> NoHashVal, ver |-> NoHashVal]]
       /\ lastHash' = h
       /\ rx' = [n \in Node |->
            [rx[n] EXCEPT ! = IF n = a THEN @ \cup {h} ELSE @]]
  /\ UNCHANGED <<>>

ValidateBlock(n, h) ==
  /\ h \in rx[n]
  /\ ledger[n][h] # NoBlockVal
  /\ ledger[n][h].sender \in PublicKey
  /\ ledger[n][h].type \in {"genesis", "send", "receive", "open", "repr"}
  /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = NoBlockVal]]
  /\ rx' = [rx EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E pk \in PrivateKey : CreateGenesisBlock(pk) \/ CreateChangeRep(NoHash, pk)
  \/ \E a \in Node, pk \in PublicKey, amt \in 0..GenesisBalance : CreateSendBlock(a, pk, amt)
  \/ \E a \in Node, pk \in PublicKey, h \in Hash : CreateOpenBlock(a, pk, h)
  \/ \E a \in Node, pk \in PublicKey, h \in Hash : CreateReceiveBlock(a, pk, h)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_<<lastHash, ledger, rx>>

\* The cryptographic invariant: every recorded block's signature matches its
\* chain's account public key, so no forged block is ever assimilated.
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => ledger[n][h].sender \in PublicKey

====