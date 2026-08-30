---- MODULE Nano ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* BlockType and BlockData model the limited shape space of a Nano block,
\* where different block types carry different required fields.
BlockType == {"GENESIS", "SEND", "OPEN", "RECEIVE", "CHANGE"}

\* Block is the stored representation; Received is the in-flight representation
\* (the sender may not yet have validated it against their ledger copy).
Block == [type: BlockType, pubkey: PublicKey, prev: Hash, target: PublicKey,
           amount: 1..GenesisBalance, hash: Hash, signature: PrivateKey]
Received == [type: BlockType, pubkey: PublicKey, prev: Hash, target: PublicKey,
             amount: 1..GenesisBalance, hash: Hash, signature: PrivateKey]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
  /\ received \in [Node -> [Hash -> Received \cup {NoHashVal}]]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> [h \in Hash |-> NoHashVal]]

\* Balance is calculated by walking a chain backwards from its head.
RECURSIVE Balance(_)
Balance(a, h) ==
  IF h = NoHash THEN 0
  ELSE IF LedgerLookup(a, h).type = "SEND" THEN Balance(a, LedgerLookup(a, h).prev) - LedgerLookup(a, h).amount
  ELSE IF LedgerLookup(a, h).type = "RECEIVE" THEN Balance(a, LedgerLookup(a, h).prev) + LedgerLookup(a, h).amount
  ELSE Balance(a, LedgerLookup(a, h).prev)

\* The operator that the .cfg file substitutes in is not a primitive: it must be
\* a total function (hence the NoHash sentinel) so it can be substituted out.
\* Its concrete shape is deliberately left to the .cfg file.
LedgerLookup(a, h) == IF h = NoHash THEN NoBlock ELSE ledger[a][h]

ReceivedAny(h) == \E n \in Node : received[n][h] # NoHashVal

AllChainsSane ==
  \A n \in Node, h \in Hash :
    ledger[n][h] # NoBlock =>
      /\ ledger[n][h].pubkey \in PublicKey
      /\ LedgerLookup(ledger[n][h].pubkey, ledger[n][h].prev) # NoBlock
      /\ ledger[n][h].type \in BlockType
      /\ ledger[n][h].hash = h

CreateGenesisBlock ==
  /\ lastHash = NoHash
  /\ \E n \in Node, k \in PrivateKey :
       /\ lastHash' = CalculateHash([type |-> "GENESIS", pubkey |-> k, prev |-> NoHash, target |-> k,
                                     amount |-> GenesisBalance, hash |-> NoHash, signature |-> NoHash])
       /\ \A m \in Node :
            ledger' = [ledger EXCEPT ![m] = [ledger[m] EXCEPT ![lastHash'] =
                            [type |-> "GENESIS", pubkey |-> k, prev |-> NoHash, target |-> k, amount |-> GenesisBalance,
                             hash |-> lastHash', signature |-> k]]]

CreateSendBlock ==
  /\ \E n \in Node, k \in PrivateKey, dest \in PublicKey, amt \in 1..GenesisBalance :
       /\ LedgerLookup(k, lastHash) # NoBlock
       /\ lastHash' = CalculateHash([type |-> "SEND", pubkey |-> k, prev |-> lastHash, target |-> dest,
                                     amount |-> amt, hash |-> NoHash, signature |-> NoHash])
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
                              [type |-> "SEND", pubkey |-> k, prev |-> lastHash, target |-> dest, amount |-> amt,
                               hash |-> lastHash', signature |-> k]]]
       /\ received' = [received EXCEPT ![n] = [received[n] EXCEPT ![lastHash'] =
                              [type |-> "SEND", pubkey |-> k, prev |-> lastHash, target |-> dest, amount |-> amt,
                               hash |-> lastHash', signature |-> k]]]

CreateOpenBlock ==
  /\ \E n \in Node, k \in PrivateKey, source \in PublicKey, amt \in 1..GenesisBalance :
       /\ LedgerLookup(k, lastHash) # NoBlock
       /\ lastHash' = CalculateHash([type |-> "OPEN", pubkey |-> k, prev |-> NoHash, target |-> source,
                                     amount |-> amt, hash |-> NoHash, signature |-> NoHash])
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
                              [type |-> "OPEN", pubkey |-> k, prev |-> NoHash, target |-> source, amount |-> amt,
                               hash |-> lastHash', signature |-> k]]]
       /\ received' = [received EXCEPT ![n] = [received[n] EXCEPT ![lastHash'] =
                              [type |-> "OPEN", pubkey |-> k, prev |-> NoHash, target |-> source, amount |-> amt,
                               hash |-> lastHash', signature |-> k]]]

CreateReceiveBlock ==
  /\ \E n \in Node, k \in PrivateKey, source \in PublicKey, amt \in 1..GenesisBalance :
       /\ LedgerLookup(k, lastHash) # NoBlock
       /\ lastHash' = CalculateHash([type |-> "RECEIVE", pubkey |-> k, prev |-> lastHash, target |-> source,
                                     amount |-> amt, hash |-> NoHash, signature |-> NoHash])
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
                              [type |-> "RECEIVE", pubkey |-> k, prev |-> lastHash, target |-> source, amount |-> amt,
                               hash |-> lastHash', signature |-> k]]]
       /\ received' = [received EXCEPT ![n] = [received[n] EXCEPT ![lastHash'] =
                              [type |-> "RECEIVE", pubkey |-> k, prev |-> lastHash, target |-> source, amount |-> amt,
                               hash |-> lastHash', signature |-> k]]]

CreateChangeRepresentativeBlock ==
  /\ \E n \in Node, k \in PrivateKey :
       /\ LedgerLookup(k, lastHash) # NoBlock
       /\ lastHash' = CalculateHash([type |-> "CHANGE", pubkey |-> k, prev |-> lastHash, target |-> k,
                                     amount |-> 0, hash |-> NoHash, signature |-> NoHash])
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash'] =
                              [type |-> "CHANGE", pubkey |-> k, prev |-> lastHash, target |-> k, amount |-> 0,
                               hash |-> lastHash', signature |-> k]]]
       /\ received' = [received EXCEPT ![n] = [received[n] EXCEPT ![lastHash'] =
                              [type |-> "CHANGE", pubkey |-> k, prev |-> lastHash, target |-> k, amount |-> 0,
                               hash |-> lastHash', signature |-> k]]]

\* Processing validates against the local copy first; a sent block whose
\* reference is not in the local copy is discarded and will be rebroadcast by the
\* originating node's own copy.
ProcessSendBlock ==
  /\ \E n \in Node, h \in Hash :
       /\ received[n][h] # NoHashVal
       /\ ~ReceivedAny(h)
       /\ LET r == received[n][h] IN
            /\ r.type = "SEND"
            /\ r.signature = r.pubkey
            /\ LedgerLookup(r.pubkey, r.prev) # NoBlock
            /\ r.amount <= Balance(r.pubkey, r.prev)
            /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = r]]
       /\ received' = [received EXCEPT ![n] = [received[n] EXCEPT ![h] = NoHashVal]]
       /\ UNCHANGED lastHash

ProcessOpenBlock ==
  /\ \E n \in Node, h \in Hash :
       /\ received[n][h] # NoHashVal
       /\ ~ReceivedAny(h)
       /\ LET r == received[n][h] IN
            /\ r.type = "OPEN"
            /\ r.signature = r.pubkey
            /\ LedgerLookup(r.pubkey, NoHash) = NoBlock
            /\ LedgerLookup(r.target, r.prev) # NoBlock
            /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = r]]
       /\ received' = [received EXCEPT ![n] = [received[n] EXCEPT ![h] = NoHashVal]]
       /\ UNCHANGED lastHash

ProcessReceiveBlock ==
  /\ \E n \in Node, h \in Hash :
       /\ received[n][h] # NoHashVal
       /\ ~ReceivedAny(h)
       /\ LET r == received[n][h] IN
            /\ r.type = "RECEIVE"
            /\ r.signature = r.pubkey
            /\ LedgerLookup(r.pubkey, r.prev) # NoBlock
            /\ LedgerLookup(r.target, r.prev) # NoBlock
            /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = r]]
       /\ received' = [received EXCEPT ![n] = [received[n] EXCEPT ![h] = NoHashVal]]
       /\ UNCHANGED lastHash

ProcessChangeRepresentativeBlock ==
  /\ \E n \in Node, h \in Hash :
       /\ received[n][h] # NoHashVal
       /\ ~ReceivedAny(h)
       /\ LET r == received[n][h] IN
            /\ r.type = "CHANGE"
            /\ r.signature = r.pubkey
            /\ LedgerLookup(r.pubkey, r.prev) # NoBlock
            /\ ledger' = [ledger EXCEPT ![n] = [ledger[n] EXCEPT ![h] = r]]
       /\ received' = [received EXCEPT ![n] = [received[n] EXCEPT ![h] = NoHashVal]]
       /\ UNCHANGED lastHash

Next ==
  \/ CreateGenesisBlock
  \/ CreateSendBlock
  \/ CreateOpenBlock
  \/ CreateReceiveBlock
  \/ CreateChangeRepresentativeBlock
  \/ ProcessSendBlock
  \/ ProcessOpenBlock
  \/ ProcessReceiveBlock
  \/ ProcessChangeRepresentativeBlock

Spec == Init /\ [][Next]_vars

SafetyInvariant == AllChainsSane

====