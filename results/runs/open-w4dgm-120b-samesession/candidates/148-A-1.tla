---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* The issuer computes a new hash from block data and the previous hash so
\* different hash implementations can be substituted via the .cfg file.
CalculateHashImpl(x, h) == CalculateHash[x, h]

\* A block is the record handed around the network, with a hash that orders
\* it relative to the block it references (its "previous block").
\* Balances are derived later by walking the account chain from the start.
Block == [prev : Hash \cup {NoHash}, acct : PublicKey, kind : {"send", "open", "receive", "change"}, amt : Nat, sig : PrivateKey]

ChainHashes(a) == {x.hash : x \in {y \in [hash : Hash, acct : PublicKey] : y.acct = a}}
ChainHashesUnion == UNION {ChainHashes(a) : a \in PublicKey}

RECURSIVE SumBalances(_)
SumBalances(S) ==
    IF S = {} THEN 0
    ELSE LET a == CHOOSE x \in S : TRUE
         IN ChainBalance(a) + SumBalances(S \ {a})

RECURSIVE ChainBalance(_)
ChainBalance(a) ==
    IF a \notin ChainHashesUnion THEN 0
    ELSE LET h == CHOOSE x \in ChainHashesUnion : x.acct = a
         IN IF Ledger[NoHash][a].kind = "open" THEN 0 ELSE Ledger[NoHash][a].amt + ChainBalance(a)

TypeOK ==
    /\ LastHash \in Hash \cup {NoHash}
    /\ Ledger \in [Hash -> [hash : Hash \cup {NoHash}, acct : PublicKey, kind : {"send", "open", "receive", "change"}, amt : Nat, sig : PrivateKey]]
    /\ \A n \in Node : Received[n] \subseteq [hash : Hash, acct : PublicKey, kind : {"send", "open", "receive", "change"}, amt : Nat, sig : PrivateKey]

Init ==
    /\ LastHash = NoHash
    /\ Ledger = [x \in Hash |-> NoBlockVal]
    /\ Received = [n \in Node |-> {}]

\* The genesis block is the one block everyone gets at the same time.
CreateGenesisBlock(n) ==
    /\ LastHash = NoHash
    /\ LET h == CalculateHashImpl([sender |-> n, kind |-> "send"], NoHash) IN
         /\ Ledger' = [Ledger EXCEPT ![NoHash] = [hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "open", amt |-> GenesisBalance, sig |-> NodeKey[n]]]
         /\ LastHash' = h
    /\ UNCHANGED Received

CreateSendBlock(n, a) ==
    /\ LET prev == Ledger[ChainHashesUnion \cap ChainHashes[PublicKeyOf[NodeKey[n]]]].hash IN
       /\ ChainBalance(PublicKeyOf[NodeKey[n]]) >= a
       /\ \E amt \in 1..a :
            /\ LET h == CalculateHashImpl([sender |-> n, kind |-> "send"], prev) IN
               /\ Ledger' = [Ledger EXCEPT ![prev] = [hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "send", amt |-> amt, sig |-> NodeKey[n]]]
               /\ LastHash' = h
            /\ Received' = [m \in Node |-> Received[m] \cup {[hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "send", amt |-> amt, sig |-> NodeKey[n]]}]
    /\ UNCHANGED <<>>

CreateOpenBlock(n, sendHash) ==
    /\ Ledger[sendHash].kind = "send"
    /\ Ledger[sendHash].acct # PublicKeyOf[NodeKey[n]]
    /\ LET h == CalculateHashImpl([sender |-> n, kind |-> "open"], NoHash) IN
         /\ Ledger' = [Ledger EXCEPT ![NoHash] = [hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "open", amt |-> 0, sig |-> NodeKey[n]]]
         /\ LastHash' = h
    /\ Received' = [m \in Node |-> Received[m] \cup {[hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "open", amt |-> 0, sig |-> NodeKey[n]]}]
    /\ UNCHANGED <<>>

CreateReceiveBlock(n, sendHash) ==
    /\ Ledger[sendHash].kind = "send"
    /\ Ledger[sendHash].acct # PublicKeyOf[NodeKey[n]]
    /\ ~ \E b \in ChainHashes[PublicKeyOf[NodeKey[n]]] : Ledger[b].kind = "receive" /\ Ledger[b].prev = sendHash
    /\ LET h == CalculateHashImpl([sender |-> n, kind |-> "receive"], ChainHashesUnion \cap ChainHashes[PublicKeyOf[NodeKey[n]]]) IN
         /\ Ledger' = [Ledger EXCEPT ![ChainHashesUnion \cap ChainHashes[PublicKeyOf[NodeKey[n]]]].hash = [hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "receive", amt |-> Ledger[sendHash].amt, sig |-> NodeKey[n]]]
         /\ LastHash' = h
    /\ Received' = [m \in Node |-> Received[m] \cup {[hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "receive", amt |-> Ledger[sendHash].amt, sig |-> NodeKey[n]]}]
    /\ UNCHANGED <<>>

CreateChangeReprBlock(n) ==
    /\ LET h == CalculateHashImpl([sender |-> n, kind |-> "change"], ChainHashesUnion \cap ChainHashes[PublicKeyOf[NodeKey[n]]]) IN
         /\ Ledger' = [Ledger EXCEPT ![ChainHashesUnion \cap ChainHashes[PublicKeyOf[NodeKey[n]]]].hash = [hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "change", amt |-> 0, sig |-> NodeKey[n]]]
         /\ LastHash' = h
    /\ Received' = [m \in Node |-> Received[m] \cup {[hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "change", amt |-> 0, sig |-> NodeKey[n]]}]
    /\ UNCHANGED <<>>

ValidateBlock(n, b) ==
    /\ b.sig = NodeKey[n]
    /\ LET acc == PublicKeyOf[NodeKey[n]] IN
        /\ b.acct = acc
        /\ Ledger[b.hash] = NoBlockVal
        /\ \/ b.kind \in {"open", "change"}
           \/ /\ b.kind = "send"
              /\ ChainBalance(acc) >= b.amt
           \/ /\ b.kind = "receive"
              /\ LET pred == Ledger[b.prev] IN
                   /\ pred.kind = "send"
                   /\ pred.acct # acc
                   /\ ~ \E x \in ChainHashes[acc] : Ledger[x].kind = "receive" /\ Ledger[x].prev = b.prev
    /\ Ledger' = [Ledger EXCEPT ![b.hash] = [hash |-> b.hash, acct |-> b.acct, kind |-> b.kind, amt |-> b.amt, sig |-> b.sig]]
    /\ Received' = [Received EXCEPT ![n] = Received[n] \ {b}]
    /\ UNCHANGED LastHash

Next ==
    \/ \E n \in Node : CreateGenesisBlock(n) \/ CreateChangeReprBlock(n)
    \/ \E n \in Node, a \in 1..GenesisBalance : CreateSendBlock(n, a)
    \/ \E n \in Node, h \in Hash : CreateOpenBlock(n, h) \/ CreateReceiveBlock(n, h) \/ ValidateBlock(n, [hash |-> h, acct |-> PublicKeyOf[NodeKey[n]], kind |-> "send", amt |-> 1, sig |-> NodeKey[n]])

\* The model is intentionally tiny (GenesisBalance = 1) because the chain
\* ordering recorded in each account's block chain causes the reachable
\* state space to grow super-exponentially with the number of actions.
Spec == Init /\ [][Next]_<<LastHash, Ledger, Received>>

\* Every block sitting in any node's replicated ledger carries a signature
\* that matches the public key of the account that owns its chain.
SafetyInvariant == \A n \in Node : \A b \in Ledger : b # NoBlockVal => b.sig = PrivateOf[b.acct]

====