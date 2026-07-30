---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES
  lastHash, ledger, received

\* A block is a four-field record. The fields are chosen so that a model checker
\* can confirm the order in which a block was applied: the order is recorded
\* in each account's chain, not in a single global log.
Block ==
  [hash: Hash, signer: PublicKey, prev: Hash \cup {NoHash}, links: SUBSET Hash]

Blocks == { NoBlock } \cup (Hash \X PublicKey \X (Hash \cup {NoHash}) \X (SUBSET Hash))

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* The chain for an account is the block with that account's public key as
\* signer, whose predecessor is NoHash, followed by blocks signed by the same
\* key linked back through the prev field.
Chain(key) ==
  LET
    f[h \in Hash] ==
      IF h = NoHash THEN {{}} ELSE
        {b << h, ledger[k][h].signer >>
           : k \in Node : ledger[k][h] # NoBlockVal /\ ledger[k][h].signer = key}
    g[S \in SUBSET {[hash: Hash, signer: PublicKey]}] ==
      IF S = {} THEN 0
      ELSE LET b == CHOOSE e \in S : TRUE IN 1 + g[S \ {b}]
  IN g[f]

Balance(key) ==
  LET
    f[h \in Hash] ==
      IF h = NoHash THEN {{}} ELSE
        {b << h, ledger[k][h].signer >>
           : k \in Node : ledger[k][h] # NoBlockVal /\ ledger[k][h].signer = key}
    g[S \in SUBSET {[hash: Hash, signer: PublicKey]}] ==
      IF S = {} THEN 0
      ELSE LET b == CHOOSE e \in S : TRUE IN
           IF h = NoHash THEN g[S \ {b}]
           ELSE LET amt == CHOOSE m \in Nat : m \in {1, 2} IN amt + g[S \ {b}]
  IN g[f]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [k \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [k \in Node |-> {}]

Broadcast(b) ==
  [k \in Node |-> received[k] \cup {b}]

Validate(k, h) ==
  /\ h \in received[k]
  /\ \A o \in Node : ledger[o][h] # NoBlockVal
  /\ LET blk == ledger[CHOOSE o \in Node : ledger[o][h] # NoBlockVal][h] IN
       /\ blk.signer = CHOOSE g \in PublicKey : ledger[o][h].signer = g
       /\ \A o \in Node : ledger[o][blk.prev] # NoBlockVal
       /\ \A l \in blk.links : ledger[CHOOSE o \in Node : ledger[o][l] # NoBlockVal][l] # NoBlockVal
       /\ ledger' = [ledger EXCEPT ![k][h] = blk]
  /\ received' = [received EXCEPT ![k] = @ \ {h}]
  /\ UNCHANGED lastHash

CreateGenesis(k) ==
  /\ lastHash = NoHashVal
  /\ ledger' = [k \in Node |-> [h \in Hash |->
        IF h = NoHash THEN
          [hash |-> NoHash, signer |-> CHOOSE g \in PublicKey : TRUE,
           prev |-> NoHash, links |-> {}]
        ELSE ledger[k][h]]]
  /\ lastHash' = NoHash
  /\ UNCHANGED received

CreateSend(k, h) ==
  /\ lastHash # NoHashVal
  /\ ledger[k][lastHash] # NoBlockVal
  /\ Balance(ledger[k][lastHash].signer) >= 1
  /\ ledger' = [ledger EXCEPT ![k][h] = [hash |-> h, signer |-> ledger[k][lastHash].signer,
        prev |-> lastHash, links |-> {}]]
  /\ lastHash' = h
  /\ received' = Broadcast(h)

CreateOpen(k, h) ==
  /\ lastHash # NoHashVal
  /\ ledger[k][lastHash] # NoBlockVal
  /\ ledger[k][h] = NoBlockVal
  /\ \E s \in Hash :
       /\ ledger[CHOOSE o \in Node : ledger[o][s] # NoBlockVal][s].signer = ledger[k][lastHash].signer
       /\ ledger' = [ledger EXCEPT ![k][h] = [hash |-> h, signer |-> ledger[CHOOSE o \in Node : ledger[o][s] # NoBlockVal][s].signer,
            prev |-> NoHash, links |-> {s}]]
  /\ lastHash' = h
  /\ received' = Broadcast(h)

CreateReceive(k, h) ==
  /\ lastHash # NoHashVal
  /\ ledger[k][lastHash] # NoBlockVal
  /\ \E s \in Hash :
       /\ ledger[CHOOSE o \in Node : ledger[o][s] # NoBlockVal][s].signer = ledger[k][lastHash].signer
       /\ ledger' = [ledger EXCEPT ![k][h] = [hash |-> h, signer |-> ledger[CHOOSE o \in Node : ledger[o][s] # NoBlockVal][s].signer,
          prev |-> lastHash, links |-> {s}]]
  /\ lastHash' = h
  /\ received' = Broadcast(h)

CreateChangeRepr(k, h) ==
  /\ lastHash # NoHashVal
  /\ ledger' = [ledger EXCEPT ![k][h] = [hash |-> h, signer |-> ledger[CHOOSE o \in Node : ledger[o][lastHash] # NoBlockVal][lastHash].signer,
        prev |-> lastHash, links |-> {}]]
  /\ lastHash' = h
  /\ received' = Broadcast(h)

Next ==
  \/ \E k \in Node : CreateGenesis(k) \/ Validate(k, lastHash)
  \/ \E k \in Node, h \in Hash : CreateSend(k, h) \/ CreateOpen(k, h) \/ CreateReceive(k, h) \/ CreateChangeRepr(k, h)

Spec == Init /\ [][Next]_<<lastHash, ledger, received>>

SafetyInvariant ==
  \A k \in Node : \A h \in Hash :
    ledger[k][h] # NoBlockVal => ledger[k][h].signer \in PublicKey

====