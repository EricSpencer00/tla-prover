---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, NoBlock

\* The hash calculation is an abstract black box here; the .cfg substitutes a concrete
\* implementation into the constant symbol CalculateHash.
CalculateHash == (x, h) \in (PublicKey \X Hash) : NoHash

VARIABLES lastHash, distributedLedger, received

vars == <<lastHash, distributedLedger, received>>

Block == [kind: {"genesis", "send", "open", "receive", "change"},
          src: PUBLICKEY, dst: PUBLICKEY, prev: Hash, recv: Hash, amt: Nat,
          sig: PrivateKey]

CopyLedger(n) == [h \in Hash |-> IF h \in DOMAIN distributedLedger[n]
                                 THEN distributedLedger[n][h] ELSE NoBlockVal]

RECURSIVE ChainBalance(_, _)
ChainBalance(n, h) ==
    IF h = NoHash THEN 0
    ELSE LET b == distributedLedger[n][h] IN
         IF b.kind = "genesis" THEN GenesisBalance
         ELSE IF b.kind = "send" THEN ChainBalance(n, b.prev) - b.amt
         ELSE IF b.kind = "receive" THEN ChainBalance(n, b.prev) + b.amt
         ELSE IF b.kind = "open" THEN ChainBalance(n, b.prev)
         ELSE ChainBalance(n, b.prev)

RECURSIVE SumBalances(_)
SumBalances(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN ChainBalance(x, lastHash) + SumBalances(S \ {x})

TypeInvariant ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ distributedLedger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Block]

Init ==
    /\ lastHash = NoHash
    /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

\* Create the genesis block that holds the entire coin supply; it is written into
\* every node's ledger in one step and can never be recreated.
CreateGenesisBlock ==
    /\ lastHash = NoHash
    /\ \E k \in PrivateKey, a \in PUBLICKEY :
         /\ distributedLedger' = [n \in Node |-> [lastHash |-> [kind |-> "genesis", src |-> a, dst |-> a,
                                                                prev |-> NoHash, recv |-> NoHash, amt |-> GenesisBalance,
                                                                sig |-> k]]]
    /\ lastHash' = CalculateHash(a, NoHash)
    /\ UNCHANGED received

CreateSendBlock(n, k, dst, amt) ==
    /\ lastHash # NoHash
    /\ k \in PrivateKey
    /\ dst \in PUBLICKEY
    /\ amt \in 1..GenesisBalance
    /\ ChainBalance(n, lastHash) >= amt
    /\ LET h == CalculateHash(dst, lastHash) IN
       /\ distributedLedger' = [distributedLedger EXCEPT ![n][h] =
              [kind |-> "send", src |-> PublicKey[k], dst |-> dst,
               prev |-> lastHash, recv |-> NoHash, amt |-> amt, sig |-> k]]
       /\ received' = [m \in Node |-> received[m] \cup {[kind |-> "send", src |-> PublicKey[k], dst |-> dst,
                                                      prev |-> lastHash, recv |-> NoHash, amt |-> amt, sig |-> k]}]
       /\ lastHash' = h

CreateOpenBlock(n, k, src, recv) ==
    /\ lastHash # NoHash
    /\ k \in PrivateKey
    /\ src \in PUBLICKEY
    /\ recv \in {lastHash}
    /\ LET h == CalculateHash(src, lastHash) IN
       /\ distributedLedger' = [distributedLedger EXCEPT ![n][h] =
              [kind |-> "open", src |-> src, dst |-> PublicKey[k],
               prev |-> NoHash, recv |-> recv, amt |-> GenesisBalance, sig |-> k]]
       /\ received' = [m \in Node |-> received[m] \cup {[kind |-> "open", src |-> src, dst |-> PublicKey[k],
                                                      prev |-> NoHash, recv |-> recv, amt |-> GenesisBalance, sig |-> k]}]
       /\ lastHash' = h

CreateReceiveBlock(n, k, src, amt, recv) ==
    /\ lastHash # NoHash
    /\ k \in PrivateKey
    /\ src \in PUBLICKEY
    /\ amt \in 1..GenesisBalance
    /\ recv \in {lastHash}
    /\ LET h == CalculateHash(src, lastHash) IN
       /\ distributedLedger' = [distributedLedger EXCEPT ![n][h] =
              [kind |-> "receive", src |-> src, dst |-> PublicKey[k],
               prev |-> lastHash, recv |-> recv, amt |-> amt, sig |-> k]]
       /\ received' = [m \in Node |-> received[m] \cup {[kind |-> "receive", src |-> src, dst |-> PublicKey[k],
                                                      prev |-> lastHash, recv |-> recv, amt |-> amt, sig |-> k]}]
       /\ lastHash' = h

CreateChangeBlock(n, k) ==
    /\ lastHash # NoHash
    /\ k \in PrivateKey
    /\ LET h == CalculateHash(PublicKey[k], lastHash) IN
       /\ distributedLedger' = [distributedLedger EXCEPT ![n][h] =
              [kind |-> "change", src |-> PublicKey[k], dst |-> PublicKey[k],
               prev |-> lastHash, recv |-> NoHash, amt |-> GenesisBalance, sig |-> k]]
       /\ received' = [m \in Node |-> received[m] \cup {[kind |-> "change", src |-> PublicKey[k], dst |-> PublicKey[k],
                                                      prev |-> lastHash, recv |-> NoHash, amt |-> GenesisBalance, sig |-> k]}]
       /\ lastHash' = h

\* Validation is per node against its own local copy (including a full chain walk for
\* balance checks), so a node whose copy deviates from the true chain is exactly the
\* node that will reject a block that otherwise looks structurally valid.
ValidateBlock(n, b) ==
    /\ b \in received[n]
    /\ b.sig \in PrivateKey
    /\ PublicKey[b.sig] = b.src
    /\ b.kind \in {"send", "open", "receive", "change"}
    /\ LET srcChainBal == ChainBalance(n, b.recv) IN
         (b.kind = "send" => srcChainBal >= b.amt)
    /\ b.kind \in {"send", "receive"} => b.amt \in 1..GenesisBalance
    /\ b.kind \in {"open", "receive"} => b.recv # NoHash
    /\ b.kind \in {"genesis", "change"} => b.amt = GenesisBalance
    /\ distributedLedger' = [distributedLedger EXCEPT ![n][CalculateHash(b.dst, b.prev)] = b]
    /\ received' = [received EXCEPT ![n] = @ \ {b}]
    /\ UNCHANGED lastHash

Validate(n) == \E b \in Block : ValidateBlock(n, b)

Next ==
    \/ CreateGenesisBlock
    \/ \E n \in Node, k \in PrivateKey, dst \in PUBLICKEY, amt \in 1..GenesisBalance : CreateSendBlock(n, k, dst, amt)
    \/ \E n \in Node, k \in PrivateKey, src \in PUBLICKEY, recv \in {lastHash} : CreateOpenBlock(n, k, src, recv)
    \/ \E n \in Node, k \in PrivateKey, src \in PUBLICKEY, amt \in 1..GenesisBalance, recv \in {lastHash} :
         CreateReceiveBlock(n, k, src, amt, recv)
    \/ \E n \in Node, k \in PrivateKey : CreateChangeBlock(n, k)
    \/ \E n \in Node : Validate(n)

Spec == Init /\ [][Next]_vars

\* Every block in every node's ledger must have a signature that matches the
\* account key it claims to belong to -- a block accepted on a stale copy fails
\* this in exactly the same way as one with a forged signature.
SafetyInvariant == \A n \in Node : \A h \in Hash :
    distributedLedger[n][h] # NoBlockVal => PublicKey[distributedLedger[n][h].sig] = distributedLedger[n][h].src

====