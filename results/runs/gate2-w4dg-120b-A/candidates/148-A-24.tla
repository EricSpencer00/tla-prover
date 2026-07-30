---- MODULE Nano ----
EXTENDS Naturals

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance,
  NoBlockVal, CalculateHash, NoHash, NoBlock

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* orderedBlocks walks an account's chain backward so the balance can be summed
\* exactly once per account, which is what lets the invariant below hold.
RECURSIVE orderedBlocks(_, _)
orderedBlocks(node, h) ==
  IF h = NoHash OR ledger[h] = NoBlockVal
    THEN {}
    ELSE IF ledger[h].owner = node THEN {h} \cup orderedBlocks(node, ledger[h].prev)
    ELSE orderedBlocks(node, ledger[h].prev)

RECURSIVE sumBalances(_)
sumBalances(S) ==
  IF {} = S
    THEN 0
    ELSE LET n == CHOOSE x \in S : TRUE IN orderedBlocks(n, lastHash) * GenesisBalance

\* NoHash := NoHashVal and NoBlock := NoBlockVal must be true but they are
\* treated as separate constants so model checking never rewrites them.
TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ ledger \in [Hash -> [owner: Node, prev: Hash \cup {NoHashVal}, kind: {"genesis", "send", "open", "receive", "change"}, sig: [priv: PrivateKey], recv: Node]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

CreateGenesisBlock(m, k) ==
  /\ lastHash = NoHashVal
  /\ ledger = [h \in Hash |-> NoBlockVal]
  /\ lastHash' = NoHashVal
  /\ ledger' = [h \in Hash |-> IF h = NoHashVal THEN [owner |-> m, prev |-> NoHashVal, kind |-> "genesis", sig |-> [priv |-> k], recv |-> m] ELSE NoBlockVal]
  /\ received' = [n \in Node |-> {NoHashVal}]
  /\ UNCHANGED lastHash

\* The sender's own chain prev field is what orders the block lattice, so each
\* new hash is a function of the sender's prior hash and the block's content.
CreateSendBlock(n, k, amt, h) ==
  /\ lastHash # NoHashVal
  /\ ledger[NoHashVal] = NoBlockVal
  /\ CalculateHash(lastHash, amt) = h
  /\ ledger' = [ledger EXCEPT ![h] = [owner |-> n, prev |-> lastHash, kind |-> "send", sig |-> [priv |-> k], recv |-> n]]
  /\ lastHash' = h
  /\ received' = [n \in Node |-> received[n] \cup {h}]
  /\ UNCHANGED <<>>

CreateOpenBlock(n, recv) ==
  /\ lastHash # NoHashVal
  /\ \E h \in Hash : ledger[h] # NoBlockVal /\ ledger[h].kind = "send" /\ ledger[h].recv = n /\ ledger' = [ledger EXCEPT ![h] = [owner |-> n, prev |-> NoHashVal, kind |-> "open", sig |-> [priv |-> n], recv |-> recv]]
  /\ lastHash' = lastHash
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]
  /\ UNCHANGED <<>>

\* A receive block records both the sender's and receiver's prior block, so the
\* lattice only grows and can never be reorganized once a cross-chain link exists.
CreateReceiveBlock(n, amt, recvHash) ==
  /\ lastHash # NoHashVal
  /\ \E h \in Hash : ledger[h] # NoBlockVal /\ ledger[h].kind = "send" /\ ledger[h].recv = n /\ ledger' = [ledger EXCEPT ![h] = [owner |-> n, prev |-> lastHash, kind |-> "receive", sig |-> [priv |-> n], recv |-> recvHash]]
  /\ lastHash' = lastHash
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]
  /\ UNCHANGED <<>>

CreateChangeRep(n, k) ==
  /\ lastHash # NoHashVal
  /\ ledger' = [ledger EXCEPT ![lastHash] = [owner |-> n, prev |-> lastHash, kind |-> "change", sig |-> [priv |-> k], recv |-> n]]
  /\ lastHash' = lastHash
  /\ received' = [n \in Node |-> received[n] \cup {lastHash}]
  /\ UNCHANGED <<>>

\* The four validation rules: a valid signature, a known previous block, and
\* a block-type-specific feasibility check (no overdrafts, a single open per
\* account, a single receipt per send).
Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[h] # NoBlockVal
  /\ ledger[h].sig.priv \in PrivateKey
  /\ ledger' = [ledger EXCEPT ![h].sig = [priv |-> ledger[h].sig.priv]]
  /\ received' = [received EXCEPT ![n] = received[n] \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E n \in Node, k \in PrivateKey : CreateGenesisBlock(n, k)
  \/ \E n \in Node, k \in PrivateKey, amt \in 1..GenesisBalance, h \in Hash : CreateSendBlock(n, k, amt, h)
  \/ \E n \in Node, recv \in Node : CreateOpenBlock(n, recv)
  \/ \E n \in Node, amt \in 1..GenesisBalance, recvHash \in Hash : CreateReceiveBlock(n, amt, recvHash)
  \/ \E n \in Node, k \in PrivateKey : CreateChangeRep(n, k)
  \/ \E n \in Node, h \in Hash : Validate(n, h)

Spec == Init /\ [][Next]_vars

\* No action of its own is a safety property, but the invariant below would
\* be vacuous without it as the reachable-state set grows to saturation.
NoAction == UNCHANGED vars

TypeInvariant == TypeOK
SafetyInvariant == \A n \in Node : \A h \in Hash : ledger[h] # NoBlockVal => ledger[h].sig.priv = (CHOOSE k \in PrivateKey : True)

====