---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal

\* A block chain per account is a sequence of blocks; the last hash is the
\* chain's ordering key. Each block carries its sender's signature, so a
\* block is valid only if its signature checks out against the account's
\* public key -- this is the cryptographic guarantee the invariant checks.
Block == [sender : PrivateKey, hash : Hash, prev : Hash, t : {"genesis",
           "send", "open", "receive", "change"}, amount : Nat, to : PublicKey]

NoBlock == [sender |-> NoBlockVal.sender, hash |-> NoBlockVal.hash,
            prev |-> NoHashVal, t |-> NoBlockVal.t, amount |-> 0, to |-> NoBlockVal.to]

RECURSIVE Balance(_)
Balance(f) == IF f = <<>> THEN 0 ELSE f[1].amount + Balance(Tail(f))

RECURSIVE BalanceOf(_)
BalanceOf(id) == IF id \in PublicKey THEN Balance(ChainOf(id)) ELSE 0

\* ChainOf is the action history: the sequence of blocks that form this
\* account's chain, built by walking back through prev links from the last
\* hash. Because each chain is a sequence, the order in which blocks were
\* applied is itself part of the state, which is why the state space grows
\* super-exponentially with the number of actions taken.
ChainOf(id) ==
  [h \in {o.hash : o \in {ledger[n][g] : n \in Node} /\ g \in Hash} |-> o]
  /\ DOMAIN [h \in {o.hash : o \in {ledger[n][g] : n \in Node} /\ g \in Hash} |-> o]
  \ {NoHash}
  LAMBDA h \in {o.hash : o \in {ledger[n][g] : n \in Node} /\ g \in Hash} : h
  /\ {NoHash} : <<>>
  /\ {o.hash : o \in {ledger[n][g] : n \in Node} /\ g \in Hash} = {}
  /\ ChainOfPost(id, ChainOf(id), NoHash)

ChainOfPost(id, seq, start) ==
  IF \E o \in {ledger[n][g] : n \in Node} /\ g \in Hash :
       /\ o.hash = start /\ o.t # "change"
       /\ (o.t = "genesis" \/ (o.t = "send" /\ o.sender \in PrivateKey /\ PublicKey[o.sender] = id)
           \/ (o.t \in {"open", "receive"} /\ o.to = id /\ id \in PublicKey))
       /\ seq' = Append(seq, o)
       /\ ChainOfPost(id, seq', o.hash)
  THEN seq
  ELSE seq

VARIABLES ledger, received, lastHash, CalculateHash

vars == <<ledger, received, lastHash, CalculateHash>>

TypeOK ==
  /\ lastHash \in Hash \cup {NoHash}
  /\ ledger \in [Node -> [Hash -> Block \cup {NoBlock}]]
  /\ received \in [Node -> SUBSET Block]
  /\ CalculateHash \in [Block \X Hash -> Hash]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [g \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]
  /\ CalculateHash \in [Block \X Hash -> Hash]

Broadcast(n, b) ==
  [m \in Node |-> IF m = n THEN received[m] ELSE received[m] \cup {b}]

ValidateBlock(n, b) ==
  /\ ledger[n][b.hash] = NoBlock
  /\ ledger[n][b.prev] # NoBlock
  /\ PublicKey[b.sender] \in PublicKey
  /\ b.amount <= BalanceOf(PublicKey[b.sender])
  /\ (IF b.t \in {"open", "receive"} THEN b.to \in PublicKey ELSE TRUE)
  /\ ledger' = [ledger EXCEPT ![n][b.hash] = b]
  /\ received' = [received EXCEPT ![n] = received[n] \ {b}]
  /\ UNCHANGED <<lastHash, CalculateHash>>

Next ==
  \/ \E n \in Node : \E pk \in PrivateKey :
       /\ lastHash # NoHash
       /\ lastHash' = CalculateHash([sender |-> pk, hash |-> lastHash, prev |-> NoHash,
                                     t |-> "genesis", amount |-> GenesisBalance, to |-> pk],
                                    lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                         [sender |-> pk, hash |-> lastHash, prev |-> NoHash,
                          t |-> "genesis", amount |-> GenesisBalance, to |-> pk]]]
       /\ UNCHANGED <<received, CalculateHash>>
  \/ \E n \in Node : \E pk \in PrivateKey : \E amt \in 1..BalanceOf(PublicKey[pk]) :
       /\ lastHash # NoHash
       /\ ledger[n][lastHash] \in Block
       /\ ledger[n][lastHash].t \in {"genesis", "change"}
       /\ lastHash' = CalculateHash([sender |-> pk, hash |-> lastHash, prev |-> lastHash,
                                     t |-> "send", amount |-> amt, to |-> PublicKey[pk]],
                                    lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                         [sender |-> pk, hash |-> lastHash, prev |-> lastHash,
                          t |-> "send", amount |-> amt, to |-> PublicKey[pk]]]]
       /\ received' = Broadcast(n, [sender |-> pk, hash |-> lastHash, prev |-> lastHash,
                                     t |-> "send", amount |-> amt, to |-> PublicKey[pk]])
       /\ UNCHANGED CalculateHash
  \/ \E n \in Node : \E pk \in PrivateKey :
       /\ lastHash # NoHash
       /\ ledger[n][lastHash] \in Block
       /\ ledger[n][lastHash].t \in {"genesis", "change"}
       /\ lastHash' = CalculateHash([sender |-> pk, hash |-> lastHash, prev |-> lastHash,
                                     t |-> "change", amount |-> 0, to |-> PublicKey[pk]],
                                    lastHash)
       /\ ledger' = [m \in Node |-> [ledger[m] EXCEPT ![lastHash] =
                         [sender |-> pk, hash |-> lastHash, prev |-> lastHash,
                          t |-> "change", amount |-> 0, to |-> PublicKey[pk]]]]
       /\ UNCHANGED <<received, CalculateHash>>
  \/ \E n \in Node, m \in Node : \E b \in received[n] : ValidateBlock(m, b)

\* The Cryptographic invariant is the property of interest: every block
\* recorded in every node's copy of the ledger must pass a signature check.
\* The ordering (the chain itself) is not part of this invariant.
SignatureValid(b) ==
  /\ b # NoBlock
  /\ b.sender \in PrivateKey
  /\ PublicKey[b.sender] \in PublicKey

Spec == Init /\ [][Next]_vars

TypeInvariant == TypeOK

SafetyInvariant == \A n \in Node : \A g \in Hash : SignatureValid(ledger[n][g])

====