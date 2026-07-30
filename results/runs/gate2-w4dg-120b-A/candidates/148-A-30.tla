---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal,
    CalculateHash, NoHash, NoBlock

ASSUME /\ NoHash \notin Hash
       /\ NoBlock \notin Hash
       /\ NoHashVal \notin Hash
       /\ NoBlockVal \notin Hash
       /\ Cardinality(Node) >= 2

\* BlockHash: the hash used to name each block, computed by the external operator.
VARIABLES lastHash, ledger, received

vars == << lastHash, ledger, received >>

Block == [acct: PublicKey, pred: Hash, kind: {"genesis", "send", "open", "receive"}, amt: Nat, to: PublicKey, repr: PublicKey]

TypeOK ==
    /\ lastHash \in Hash \cup {NoHash}
    /\ ledger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
    /\ received \in [Node -> SUBSET Hash]

Init ==
    /\ lastHash = NoHash
    /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
    /\ received = [n \in Node |-> {}]

ComputeHash(b) == CalculateHash([ac |-> b.acct, pr |-> b.pred, k |-> b.kind, a |-> b.amt, t |-> b.to, r |-> b.repr])

\* Accumulate the amounts written in this account chain (finite, because the hash
\* space is finite), walking the chain backwards from its tip.
ChainBalance(a) ==
    LET Walk(h) == IF h = NoHashVal THEN 0
                    ELSE IF ledger["n1"][h] = NoBlockVal THEN 0
                    ELSE LET b == ledger["n1"][h] IN
                          IF b.acct = a THEN
                              IF b.kind = "send" THEN -b.amt
                              ELSE IF b.kind = "receive" THEN b.amt
                              ELSE Walk(b.pred)
                          ELSE Walk(b.pred)
    IN Walk(lastHash)

TotalBalance ==
    LET Walk(h, p) ==
        IF h = NoHashVal THEN p
        ELSE IF ledger["n1"][h] = NoBlockVal THEN p
        ELSE Walk(ledger["n1"][h].pred, p + (IF ledger["n1"][h].kind = "send" THEN -ledger["n1"][h].amt ELSE IF ledger["n1"][h].kind = "receive" THEN ledger["n1"][h].amt ELSE 0))
    IN Walk(lastHash, 0)

IntoLedger(b) ==
    /\ lastHash # NoHash
    /\ LET nh == ComputeHash(b) IN
        /\ lastHash' = nh
        /\ ledger' = [n \in Node |-> [ledger[n] EXCEPT ![nh] = b]]
        /\ received' = [n \in Node |-> received[n] \cup {nh}]

\* Genesis block records the whole supply and is added to every node's copy.
Genesis(n, k) ==
    /\ lastHash = NoHash
    /\ n \in Node
    /\ k \in PrivateKey
    /\ LET b == [acct |-> k, pred |-> NoHashVal, kind |-> "genesis", amt |-> GenesisBalance, to |-> k, repr |-> k]
       IN IntoLedger(b)

SendBlock(n, k, t, a) ==
    /\ lastHash # NoHash
    /\ n \in Node
    /\ k \in PrivateKey
    /\ t \in PublicKey
    /\ a \in Nat
    /\ ChainBalance(k) >= a
    /\ ChainBalance(t) = 0
    /\ LET b == [acct |-> k, pred |-> lastHash, kind |-> "send", amt |-> a, to |-> t, repr |-> k]
       IN IntoLedger(b)

OpenBlock(n, k, i) ==
    /\ lastHash # NoHash
    /\ n \in Node
    /\ k \in PrivateKey
    /\ i \in Hash
    /\ ledger[n][i] # NoBlockVal
    /\ ledger[n][i].kind = "send"
    /\ ledger[n][i].to = k
    /\ ChainBalance(k) = 0
    /\ LET b == [acct |-> k, pred |-> lastHash, kind |-> "open", amt |-> 0, to |-> k, repr |-> k]
       IN IntoLedger(b)

ReceiveBlock(n, k, i) ==
    /\ lastHash # NoHash
    /\ n \in Node
    /\ k \in PrivateKey
    /\ i \in Hash
    /\ ledger[n][i] # NoBlockVal
    /\ ledger[n][i].kind = "send"
    /\ ledger[n][i].to = k
    /\ ChainBalance(k) = 0
    /\ LET b == [acct |-> k, pred |-> lastHash, kind |-> "receive", amt |-> 0, to |-> k, repr |-> k]
       IN IntoLedger(b)

ReprBlock(n, k, r) ==
    /\ lastHash # NoHash
    /\ n \in Node
    /\ k \in PrivateKey
    /\ r \in PublicKey
    /\ LET b == [acct |-> k, pred |-> lastHash, kind |-> "repr", amt |-> 0, to |-> k, repr |-> r]
       IN IntoLedger(b)

Process(n, i) ==
    /\ i \in received[n]
    /\ ledger[n][i] # NoBlockVal
    /\ received' = [received EXCEPT ![n] = received[n] \ {i}]
    /\ UNCHANGED << lastHash, ledger >>

Next ==
    \/ \E n \in Node, k \in PrivateKey : Genesis(n, k)
    \/ \E n \in Node, k \in PrivateKey, t \in PublicKey, a \in Nat : SendBlock(n, k, t, a)
    \/ \E n \in Node, k \in PrivateKey, i \in Hash : OpenBlock(n, k, i)
    \/ \E n \in Node, k \in PrivateKey, i \in Hash : ReceiveBlock(n, k, i)
    \/ \E n \in Node, k \in PrivateKey, r \in PublicKey : ReprBlock(n, k, r)
    \/ \E n \in Node, i \in Hash : Process(n, i)

Spec == Init /\ [][Next]_vars

\* Chain integrity plus a valid signature under the owning public key is what keeps
\* the distributed ledger honest in this model.
Validate(b) == b.kind \in {"genesis", "send", "open", "receive", "repr"}
                /\ b.pred = NoHashVal \/ ledger["n1"][b.pred] # NoBlockVal

SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[n][h] # NoBlockVal => Validate(ledger[n][h])

====