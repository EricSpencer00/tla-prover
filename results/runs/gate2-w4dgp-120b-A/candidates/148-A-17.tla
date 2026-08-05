---- MODULE Nano ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

HashBlock(p, to, amt, prev) == Hash \cup { CalculateHash(p, to, amt, prev) }

RECURSIVE ChainBalance(_, _)
ChainBalance(chain, b) ==
  IF b = NoBlock OR b = NoBlockVal \/ ~ b \in chain
  THEN 0
  ELSE LET p  == chain[b].p
           to = chain[b].to
           pb = ChainBalance(chain, chain[b].prev)
       IN IF p = to THEN pb + chain[b].amt ELSE pb - chain[b].amt

RECURSIVE AccountBalance(_)
AccountBalance(chain) ==
  LET blocks == { b \in Hash : chain[b] # NoBlock /\ chain[b].p = chain[b].to }
   IN LET sum == IF blocks = {} THEN 0
                 ELSE LET x == CHOOSE e \in blocks : TRUE
                      IN ChainBalance(chain, x) + AccountBalanceExcept(chain, { x })
       IN sum

RECURSIVE AccountBalanceExcept(_, _)
AccountBalanceExcept(chain, exc) ==
  LET blocks == { b \in Hash : chain[b] # NoBlock /\ chain[b].p = chain[b].to /\ b \notin exc }
   IN LET sum == IF blocks = {} THEN 0
                 ELSE LET x == CHOOSE e \in blocks : TRUE
                      IN ChainBalance(chain, x) + AccountBalanceExcept(chain, exc \cup { x })
       IN sum

BalanceConserved == \A n \in Node : AccountBalance(Ledger(n)) = GenesisBalance

TypeInvariant ==
  /\ lastHash \in Hash \cup { NoHash }
  /\ \A n \in Node : Ledger(n) \in [Hash -> [p: PrivateKey, to: PublicKey, amt: 0..GenesisBalance, prev: Hash \cup { NoHash }, sig: 0..2]]
  /\ \A n \in Node : Received(n) \subseteq Hash

SpecSignature(n, b) == Ledger(n)[b].sig = Ledger(n)[b].p % 3

SafetyInvariant == \A n \in Node : \A b \in Hash : Ledger(n)[b] # NoBlock => SpecSignature(n, b)

VARIABLES lastHash, Ledger, Received

Init ==
  /\ lastHash = NoHash
  /\ \A n \in Node : Ledger(n) = [h \in Hash |-> NoBlock]
  /\ \A n \in Node : Received(n) = {}

GenesisBlock ==
  /\ \A n \in Node : Ledger(n) = [h \in Hash |-> NoBlock]
  /\ \E n \in Node, k \in PrivateKey :
       /\ Ledger' = [m \in Node |-> [h \in Hash |->
                         IF h = HashBlock(k, PublicKey, GenesisBalance, NoHash) THEN [p |-> k, to |-> PublicKey, amt |-> GenesisBalance, prev |-> NoHash, sig |-> k % 3] ELSE NoBlock]]
       /\ lastHash' = HashBlock(k, PublicKey, GenesisBalance, NoHash)
       /\ Received' = [m \in Node |-> { HashBlock(k, PublicKey, GenesisBalance, NoHash) }]
  /\ UNCHANGED << >>

CreateSendBlock ==
  /\ lastHash # NoHash
  /\ \E n \in Node, k \in PrivateKey, rec \in PublicKey, amt \in 1..GenesisBalance, pht \in Hash \cup { NoHash } :
       /\ Ledger(n)[pht] = NoBlock
       /\ ChainBalance(Ledger(n), pht) - amt >= 0
       /\ LET h == HashBlock(k, rec, amt, pht) IN
            /\ h \notin { Ledger(m)[x].prev : m \in Node, x \in Hash }
            /\ lastHash' = h
            /\ Ledger' = [Ledger EXCEPT ![n][h] = [p |-> k, to |-> rec, amt |-> amt, prev |-> pht, sig |-> k % 3]]
            /\ Received' = [Received EXCEPT ![n] = Received[n] \cup { h }]
  /\ UNCHANGED << >>

CreateOpenBlock ==
  /\ lastHash # NoHash
  /\ \E n \in Node, k \in PrivateKey, pht \in Hash :
       /\ Ledger(n)[pht] = NoBlock
       /\ Ledger(n)[lastHash].to = PublicKey
       /\ LET h == HashBlock(k, PublicKey, 0, pht) IN
            /\ h \notin { Ledger(m)[x].prev : m \in Node, x \in Hash }
            /\ lastHash' = h
            /\ Ledger' = [Ledger EXCEPT ![n][h] = [p |-> k, to |-> PublicKey, amt |-> 0, prev |-> pht, sig |-> k % 3]]
            /\ Received' = [Received EXCEPT ![n] = Received[n] \cup { h }]
  /\ UNCHANGED << >>

CreateReceiveBlock ==
  /\ lastHash # NoHash
  /\ \E n \in Node, k \in PrivateKey, pht, snt \in Hash :
       /\ Ledger(n)[pht] = NoBlock
       /\ Ledger(n)[snt] = NoBlock
       /\ Ledger(n)[lastHash].to = PublicKey
       /\ Ledger(n)[snt].to = PublicKey
       /\ snt # pht
       /\ LET h == HashBlock(k, PublicKey, 0, pht) IN
            /\ h \notin { Ledger(m)[x].prev : m \in Node, x \in Hash }
            /\ lastHash' = h
            /\ Ledger' = [Ledger EXCEPT ![n][h] = [p |-> k, to |-> PublicKey, amt |-> 0, prev |-> pht, sig |-> k % 3]]
            /\ Received' = [Received EXCEPT ![n] = Received[n] \cup { h }]
  /\ UNCHANGED << >>

CreateChangeBlock ==
  /\ lastHash # NoHash
  /\ \E n \in Node, k \in PrivateKey, pht \in Hash :
       /\ Ledger(n)[pht] = NoBlock
       /\ LET h == HashBlock(k, PublicKey, 0, pht) IN
            /\ h \notin { Ledger(m)[x].prev : m \in Node, x \in Hash }
            /\ lastHash' = h
            /\ Ledger' = [Ledger EXCEPT ![n][h] = [p |-> k, to |-> PublicKey, amt |-> 0, prev |-> pht, sig |-> k % 3]]
            /\ Received' = [Received EXCEPT ![n] = Received[n] \cup { h }]
  /\ UNCHANGED << >>

ValidateBlock(n, h) ==
  /\ h \in Received(n)
  /\ Ledger(n)[h] = NoBlock
  /\ \A o \in Node : Ledger(o)[h] # NoBlock
  /\ LET b == Ledger(h)[h] IN
       /\ b.sig = b.p % 3
       /\ LET pht == Ledger(h)[b.prev] IN
            /\ IF b.prev = NoHash THEN TRUE ELSE pht # NoBlock
            /\ IF b.amt = 0 THEN TRUE ELSE b.p = b.prev.p
       /\ LET snt == Ledger(h)[lastHash] IN
            /\ IF b.to = PublicKey THEN TRUE ELSE snt # NoBlock /\ snt.to = b.to /\ snt.amt = b.amt /\ snt.prev = b.prev
  /\ Ledger' = [Ledger EXCEPT ![n][h] = Ledger(h)[h]]
  /\ Received' = [Received EXCEPT ![n] = Received[n] \ { h }]
  /\ UNCHANGED << lastHash >>

Next ==
  \/ GenesisBlock
  \/ CreateSendBlock
  \/ CreateOpenBlock
  \/ CreateReceiveBlock
  \/ CreateChangeBlock
  \/ \E n \in Node : \E h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_<< lastHash, Ledger, Received >>
====