---------------------------- MODULE Nano ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node,
  GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Owners == PublicKey
NoOwner == "noowner"
Hashes == Hash \cup {NoHash}
Accounts == PublicKey \cup {NoOwner}
BlockTypes == {"send", "receive", "open", "change", "genesis"}

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hashes -> [type: BlockTypes,
                                      owner: Owners,
                                      amount: Nat,
                                      ref: Hashes,
                                      prev: Hashes,
                                      pubkey: PublicKey,
                                      sig: PublicKey]]]
  /\ received \in [Node -> SUBSET [type: BlockTypes,
                                    owner: Owners,
                                    amount: Nat,
                                    ref: Hashes,
                                    prev: Hashes,
                                    pubkey: PublicKey,
                                    sig: PublicKey]]


RECURSIVE WalkChain(_, _, _)
WalkChain(f, chain, start) ==
  IF start = NoHash THEN 0
  ELSE LET blk == f[chain][start] IN
       blk.amount + WalkChain(f, chain, blk.prev)

RECURSIVE TotalBalance(_)
TotalBalance(f) == WalkChain(f, NoOwner, NoHash)

SigningKey(k) == CHOOSE sk \in PrivateKey : k = PUBLIC(sk)

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hashes |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

Broadcast(blk) ==
  /\ \A n \in Node : blk \notin received[n]
  /\ \A n \in Node : received' = [received EXCEPT ![n] = received[n] \cup {blk}]
  /\ UNCHANGED <<lastHash, ledger>>

ValidSignature(blk) == blk.sig = blk.pubkey

CheckBlock(n, blk, owner) ==
  /\ blk.type \in BlockTypes
  /\ ledger[n][blk.ref] # NoBlock
  /\ ledger[n][blk.prev] # NoBlock
  /\ ValidSignature(blk)
  /\ blk.pubkey = SigningKey(blk.sig)
  /\ blk.owner = owner

CreateGenesisBlock(sk) ==
  /\ lastHash = NoHash
  /\ \E n \in Node :
       /\ ~(\E h \in Hashes : ledger[n][h] # NoBlock
                                 /\ ledger[n][h].type = "genesis")
       /\ LET blk ==
            [type |-> "genesis", owner |-> SigningKey(sk), amount |-> GenesisBalance,
             ref |-> NoHash, prev |-> NoHash, pubkey |-> SigningKey(sk), sig |-> sk] IN
          /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![CalculateHash(blk, lastHash)] = blk]]
          /\ lastHash' = CalculateHash(blk, lastHash)
  /\ UNCHANGED received

CreateSendBlock(n, sk, amt, ref) ==
  /\ TotalBalance(ledger[n]) >= amt
  /\ \E h \in Hashes : ledger[n][h] = NoBlock
  /\ LET blk ==
       [type |-> "send", owner |-> SigningKey(sk), amount |-> amt,
        ref |-> ref, prev |-> lastHash, pubkey |-> SigningKey(sk), sig |-> sk] IN
     /\ ledger' = [ledger EXCEPT ![n][CalculateHash(blk, lastHash)] = blk]
     /\ lastHash' = CalculateHash(blk, lastHash)
  /\ Broadcast(blk)
  /\ UNCHANGED received

CreateOpenBlock(n, sk, ref) ==
  /\ \E h \in Hashes : ledger[n][h] = NoBlock
  /\ ledger[n][ref].type = "send"
  /\ ledger[n][ref].sig = SigningKey(sk)
  /\ LET blk ==
       [type |-> "open", owner |-> SigningKey(sk), amount |-> ledger[n][ref].amount,
        ref |-> ref, prev |-> NoHash, pubkey |-> SigningKey(sk), sig |-> sk] IN
     /\ ledger' = [ledger EXCEPT ![n][CalculateHash(blk, lastHash)] = blk]
     /\ lastHash' = CalculateHash(blk, lastHash)
  /\ Broadcast(blk)
  /\ UNCHANGED received

CreateReceiveBlock(n, sk, ref) ==
  /\ ledger[n][ref].type = "send"
  /\ ledger[n][ref].sig = SigningKey(sk)
  /\ \E h \in Hashes : ledger[n][h] = NoBlock
  /\ LET blk ==
       [type |-> "receive", owner |-> SigningKey(sk), amount |-> ledger[n][ref].amount,
        ref |-> ref, prev |-> lastHash, pubkey |-> SigningKey(sk), sig |-> sk] IN
     /\ ledger' = [ledger EXCEPT ![n][CalculateHash(blk, lastHash)] = blk]
     /\ lastHash' = CalculateHash(blk, lastHash)
  /\ Broadcast(blk)
  /\ UNCHANGED received

CreateChangeRepresentativeBlock(n, sk) ==
  /\ \E h \in Hashes : ledger[n][h] = NoBlock
  /\ LET blk ==
       [type |-> "change", owner |-> SigningKey(sk), amount |-> 0,
        ref |-> NoHash, prev |-> lastHash, pubkey |-> SigningKey(sk), sig |-> sk] IN
     /\ ledger' = [ledger EXCEPT ![n][CalculateHash(blk, lastHash)] = blk]
     /\ lastHash' = CalculateHash(blk, lastHash)
  /\ Broadcast(blk)
  /\ UNCHANGED received

Validate(n, blk) ==
  /\ ledger[n][blk.ref] = NoBlock
  /\ CheckBlock(n, blk, ledger[n][blk.ref].owner)
  /\ ledger' = [ledger EXCEPT ![n][blk.ref] = blk]
  /\ UNCHANGED <<lastHash, received>>

Process(n) ==
  \E blk \in received[n] : Validate(n, blk)

Next ==
  \/ \E sk \in PrivateKey : CreateGenesisBlock(sk)
  \/ \E n \in Node, sk \in PrivateKey :
       \/ CreateSendBlock(n, sk, 1, NoHash)
       \/ CreateOpenBlock(n, sk, NoHash)
       \/ CreateReceiveBlock(n, sk, NoHash)
       \/ CreateChangeRepresentativeBlock(n, sk)
  \/ \E n \in Node : Process(n)

Spec == Init /\ [][Next]_vars

SafetyInvariant ==
  \A n \in Node : \A h \in Hashes :
    ledger[n][h] # NoBlock => ledger[n][h].sig = ledger[n][h].pubkey

=======================================================================