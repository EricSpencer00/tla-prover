---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Per-account chains are modeled as a total function from a predecessor hash
\* (or NoHash for the first block) to the block sitting at that position.
Block == [owner : PublicKey, prevHash : Hash \cup {NoHash}, hash : Hash,
           typ : {"genesis", "send", "open", "receive", "change"}, amt : 0..GenesisBalance,
           signedBy : PrivateKey]

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

Chains == [NoHash ..> NoBlock] \cup {NoBlock}
EmptyLedger == [h \in Hash |-> NoBlock]

\* The chain of blocks owned by a public key is reconstructed from the ledger:
ChainFor(pk, h) == IF h = NoHash THEN EmptyLedger
  ELSE LET b == ledger[h] IN
       IF b = NoBlock \/ b.owner # pk THEN EmptyLedger
       ELSE [h1 \in Hash \cup {NoHash} |-> IF h1 = h THEN b
                                          ELSE ChainFor(pk, h1)]

BalanceFor(pk, h) ==
  LET ch == ChainFor(pk, h) IN
  IF ch = EmptyLedger THEN 0
  ELSE LET c == ch[h] IN
       IF c.typ = "genesis" THEN c.amt
       ELSE IF c.typ = "send" THEN BalanceFor(pk, ch[c.prevHash]) - c.amt
       ELSE IF c.typ = "receive" THEN BalanceFor(pk, ch[c.prevHash]) + c.amt
       ELSE BalanceFor(pk, ch[c.prevHash])

SumBalances == CHOOSE s \in 0..GenesisBalance : \E f \in [PublicKey -> 0..GenesisBalance] :
  (FORALL pk \in PublicKey : f[pk] = BalanceFor(pk, lastHash)) => s = f[PublicKey[1]] + f[PublicKey[2]]

TypeInvariant ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> Block \cup {NoBlockVal}]
  /\ received \in [Node -> SUBSET Hash]

\* Every block in the replicated shared ledger must carry a signature that
\* matches the public key of the account chain it sits in.
SafetyInvariant ==
  \A n \in Node : \A h \in Hash :
    ledger[h] # NoBlockVal => PublicKey[ledger[h].signedBy] = ledger[h].owner

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

CreateGenesis(pk) ==
  /\ lastHash = NoHashVal
  /\ \E sk \in PrivateKey :
       /\ PublicKey[sk] = pk
       /\ \E h0 \in Hash :
            /\ ledger[h0] = NoBlockVal
            /\ lastHash' = h0
            /\ ledger' = [ledger EXCEPT ![h0] = [owner |-> pk, prevHash |-> NoHash, hash |-> h0,
                                                   typ |-> "genesis", amt |-> GenesisBalance, signedBy |-> sk]]
            /\ UNCHANGED received

\* Account balance is re-read from the ledger, not cached per-node.
BalanceOf(pk) == BalanceFor(pk, lastHash)

CreateSend(sk, pkTo, amt) ==
  /\ lastHash # NoHashVal
  /\ amt <= BalanceOf(PublicKey[sk])
  /\ \E h1 \in Hash :
       /\ ledger[h1] = NoBlockVal
       /\ lastHash' = h1
       /\ ledger' = [ledger EXCEPT ![h1] = [owner |-> PublicKey[sk], prevHash |-> lastHash, hash |-> h1,
                                            typ |-> "send", amt |-> amt, signedBy |-> sk]]
       /\ UNCHANGED received

CreateOpen(sk, hSend) ==
  /\ lastHash # NoHashVal
  /\ ledger[hSend] # NoBlockVal
  /\ ledger[hSend].typ = "send"
  /\ ledger[hSend].owner = PublicKey[sk]
  /\ ledger[hSend].hash = hSend
  /\ ChainFor(PublicKey[sk], lastHash) = EmptyLedger
  /\ \E h1 \in Hash :
       /\ ledger[h1] = NoBlockVal
       /\ lastHash' = h1
       /\ ledger' = [ledger EXCEPT ![h1] = [owner |-> PublicKey[sk], prevHash |-> lastHash, hash |-> h1,
                                            typ |-> "open", amt |-> 0, signedBy |-> sk]]
       /\ UNCHANGED received

CreateReceive(sk, hOpen, hSend) ==
  /\ lastHash # NoHashVal
  /\ ledger[hOpen] # NoBlockVal
  /\ ledger[hOpen].typ = "open"
  /\ ledger[hOpen].owner = PublicKey[sk]
  /\ ledger[hSend] # NoBlockVal
  /\ ledger[hSend].typ = "send"
  /\ ledger[hSend].owner # PublicKey[sk]
  /\ \A h \in Hash : (ChainFor(PublicKey[sk], lastHash)[h] # NoBlock => h # hSend)
  /\ \E h1 \in Hash :
       /\ ledger[h1] = NoBlockVal
       /\ lastHash' = h1
       /\ ledger' = [ledger EXCEPT ![h1] = [owner |-> PublicKey[sk], prevHash |-> lastHash, hash |-> h1,
                                            typ |-> "receive", amt |-> ledger[hSend].amt, signedBy |-> sk]]
       /\ UNCHANGED received

CreateChange(sk) ==
  /\ lastHash # NoHashVal
  /\ \E h1 \in Hash :
       /\ ledger[h1] = NoBlockVal
       /\ lastHash' = h1
       /\ ledger' = [ledger EXCEPT ![h1] = [owner |-> PublicKey[sk], prevHash |-> lastHash, hash |-> h1,
                                            typ |-> "change", amt |-> 0, signedBy |-> sk]]
       /\ UNCHANGED received

Broadcast(h) ==
  /\ lastHash # NoHashVal
  /\ ledger[h] # NoBlockVal
  /\ \A n \in Node : h \notin received[n]
  /\ received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED <<lastHash, ledger>>

\* Validation checks signatures, chaining, and block-type-specific rules.
Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[h] # NoBlockVal
  /\ (PublicKey[ledger[h].signedBy] = ledger[h].owner)
  /\ ChainFor(ledger[h].owner, (IF h = lastHash THEN NoHash ELSE lastHash)) # EmptyLedger
  /\ /\ IF ledger[h].typ = "send" THEN ledger[h].amt <= BalanceOf(ledger[h].owner) ELSE TRUE
     /\ IF ledger[h].typ = "open" THEN ChainFor(ledger[h].owner, lastHash) = EmptyLedger ELSE TRUE
     /\ IF ledger[h].typ = "receive" THEN ledger[ledger[h].prevHash].typ = "open" ELSE TRUE
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash, ledger>>

Next ==
  \/ \E pk \in PublicKey : CreateGenesis(pk)
  \/ \E sk \in PrivateKey, pkTo \in PublicKey, amt \in 1..GenesisBalance : CreateSend(sk, pkTo, amt)
  \/ \E sk \in PrivateKey, hSend \in Hash : CreateOpen(sk, hSend)
  \/ \E sk \in PrivateKey, hOpen \in Hash, hSend \in Hash : CreateReceive(sk, hOpen, hSend)
  \/ \E sk \in PrivateKey : CreateChange(sk)
  \/ \E h \in Hash : Broadcast(h)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

====