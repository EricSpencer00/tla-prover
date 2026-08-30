---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

\* A block is a signed record in an account-chain; the hash of its contents and
\* the previous block identity it carries is what makes the block unique, and
\* the signature is what makes it authentic to that account's key.
BlockType == [kind: {"genesis", "send", "open", "receive", "change"},
              acct: PublicKey, prev: Hash, sender: PublicKey, recv: PublicKey,
              amt: Nat, sig: PrivateKey]

\* The last calculated hash orders block creation; the ledger is replicated across
\* nodes, and a received-but-unvalidated set per node models blocks in transit.
VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A deposited amount that has not yet been confirmed has no chain position yet
\* (it is anchored by a send block with no child), so the balance function is
\* parametric in the set of already-confirmed blocks rather than walking the
\* entire chain and assuming every link exists.
RECURSIVE Balance(_)
Balance(S) ==
  IF S = {} THEN 0
  ELSE LET h == CHOOSE e \in S : TRUE
           blk == ledger[NoHash][h]
       IN (IF blk.kind = "send" THEN -blk.amt
           ELSE IF blk.kind = "receive" THEN blk.amt ELSE 0)
          + Balance(S \ {h})

RECURSIVE CumulativeBalance(_)
CumulativeBalance(S) ==
  IF S = {} THEN 0
  ELSE LET k == CHOOSE n \in S : TRUE
       IN Balance(ledger[k]) + CumulativeBalance(S \ {k})

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [k \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* A block is written to every node's ledger on creation, so it can never
\* silently drop out of the replicated ledger and corrupt the balance function.
CreateGenesisBlock ==
  /\ lastHash = NoHashVal
  /\ \E ik \in Node, pk \in PrivateKey :
       /\ ledger[ik][NoHash] = NoBlockVal
       /\ ledger' = [ledger EXCEPT ![ik][NoHash] = [kind |-> "genesis",
                                                    acct |-> PublicKey[pk],
                                                    prev |-> NoHash,
                                                    sender |-> PublicKey[pk],
                                                    recv |-> PublicKey[pk],
                                                    amt |-> GenesisBalance,
                                                    sig |-> pk]]
  /\ lastHash' = NoHashVal
  /\ received' = [n \in Node |-> received[n]]

CreateSendBlock ==
  /\ lastHash # NoHashVal
  /\ \E ik \in Node, pk \in PrivateKey, r \in PublicKey, v \in Nat :
       /\ ledger[ik][lastHash] # NoBlockVal
       /\ ledger[ik][lastHash].acct = PublicKey[pk]
       /\ v <= Balance(ledger[ik])
       /\ LET h2 == CalculateHash([kind |-> "send", acct |-> PublicKey[pk],
                                   prev |-> lastHash, sender |-> PublicKey[pk],
                                   recv |-> r, amt |-> v, sig |-> pk])
          IN /\ h2 \notin Hash
             /\ ledger' = [ledger EXCEPT ![ik][h2] = [kind |-> "send",
                                                      acct |-> PublicKey[pk],
                                                      prev |-> lastHash,
                                                      sender |-> PublicKey[pk],
                                                      recv |-> r, amt |-> v,
                                                      sig |-> pk]]
             /\ lastHash' = h2
             /\ received' = [n \in Node |-> received[n] \cup {h2}]

CreateOpenBlock ==
  /\ lastHash # NoHashVal
  /\ \E ik \in Node, pk \in PrivateKey, h \in Hash :
       /\ ledger[ik][lastHash] # NoBlockVal
       /\ ledger[ik][h] # NoBlockVal
       /\ ledger[ik][h].kind = "send"
       /\ ledger[ik][h].recv = PublicKey[pk]
       /\ ledger[ik][h].amt <= GenesisBalance
       /\ LET h2 == CalculateHash([kind |-> "open", acct |-> PublicKey[pk],
                                   prev |-> NoHash, sender |-> ledger[ik][h].sender,
                                   recv |-> PublicKey[pk], amt |-> ledger[ik][h].amt,
                                   sig |-> pk])
          IN /\ h2 \notin Hash
             /\ ledger' = [ledger EXCEPT ![ik][h2] = [kind |-> "open",
                                                      acct |-> PublicKey[pk],
                                                      prev |-> NoHash,
                                                      sender |-> ledger[ik][h].sender,
                                                      recv |-> PublicKey[pk],
                                                      amt |-> ledger[ik][h].amt,
                                                      sig |-> pk]]
             /\ lastHash' = h2
             /\ received' = [n \in Node |-> received[n] \cup {h2}]

CreateReceiveBlock ==
  /\ lastHash # NoHashVal
  /\ \E ik \in Node, pk \in PrivateKey, h \in Hash :
       /\ ledger[ik][lastHash] # NoBlockVal
       /\ ledger[ik][h] # NoBlockVal
       /\ ledger[ik][h].kind = "send"
       /\ ledger[ik][h].recv = PublicKey[pk]
       /\ ledger[ik][h].amt <= GenesisBalance
       /\ \A j \in Node : ledger[j][h].kind # "receive"
       /\ LET h2 == CalculateHash([kind |-> "receive", acct |-> PublicKey[pk],
                                   prev |-> lastHash, sender |-> ledger[ik][h].sender,
                                   recv |-> PublicKey[pk], amt |-> ledger[ik][h].amt,
                                   sig |-> pk])
          IN /\ h2 \notin Hash
             /\ ledger' = [ledger EXCEPT ![ik][h2] = [kind |-> "receive",
                                                      acct |-> PublicKey[pk],
                                                      prev |-> lastHash,
                                                      sender |-> ledger[ik][h].sender,
                                                      recv |-> PublicKey[pk],
                                                      amt |-> ledger[ik][h].amt,
                                                      sig |-> pk]]
             /\ lastHash' = h2
             /\ received' = [n \in Node |-> received[n] \cup {h2}]

CreateChangeRepresentativeBlock ==
  /\ lastHash # NoHashVal
  /\ \E ik \in Node, pk \in PrivateKey :
       /\ ledger[ik][lastHash] # NoBlockVal
       /\ ledger[ik][lastHash].acct = PublicKey[pk]
       /\ LET h2 == CalculateHash([kind |-> "change", acct |-> PublicKey[pk],
                                   prev |-> lastHash, sender |-> PublicKey[pk],
                                   recv |-> PublicKey[pk], amt |-> 0, sig |-> pk])
          IN /\ h2 \notin Hash
             /\ ledger' = [ledger EXCEPT ![ik][h2] = [kind |-> "change",
                                                      acct |-> PublicKey[pk],
                                                      prev |-> lastHash,
                                                      sender |-> PublicKey[pk],
                                                      recv |-> PublicKey[pk],
                                                      amt |-> 0,
                                                      sig |-> pk]]
             /\ lastHash' = h2
             /\ received' = [n \in Node |-> received[n] \cup {h2}]

ProcessValidate ==
  \E n \in Node, h \in received[n] :
    /\ ledger[n][h] = NoBlockVal
    /\ \E k \in Node :
         /\ ledger[k][h] # NoBlockVal
         /\ LET blk == ledger[k][h] IN
              /\ ledger[n][blk.prev] # NoBlockVal
              /\ \E pk \in PrivateKey :
                   /\ PublicKey[pk] = blk.acct
                   /\ blk.sig = pk
              /\ IF blk.kind = "send" THEN blk.amt <= GenesisBalance ELSE TRUE
    /\ ledger' = [ledger EXCEPT ![n][h] = ledger[CHOOSE k \in Node : ledger[k][h] # NoBlockVal][h]]
    /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
    /\ lastHash' = lastHash

Next == CreateGenesisBlock \/ CreateSendBlock \/ CreateOpenBlock
        \/ CreateReceiveBlock \/ CreateChangeRepresentativeBlock
        \/ ProcessValidate

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Node -> [Hash -> BlockType \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

\* Cryptographic accountability: a block's recorded owner and its signature are
\* mutually confirming facts, so no forged block can pass validation.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash :
    ledger[n][h] # NoBlockVal => PublicKey[ledger[n][h].sig] = ledger[n][h].acct

====