---- MODULE Nano ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Hashes that have been calculated so far; the hash function is injective between
\* any two hash values not already in that set. The network is assumed to start
\* with a single ledger copy across all its nodes.
Hashes == Hash \cup {NoHashVal}

VARIABLES lastHash, ledger, received

vars == <<lastHash, ledger, received>>

\* A ledger is a map from block hashes to signed blocks (or the empty sentinel).
SignedBlock == [prev: Hashes, owner: PublicKey, kind: {"genesis", "send", "open", "receive", "change"}, target: PublicKey, amount: Nat]

TypeOK ==
  /\ lastHash \in Hashes
  /\ ledger \in [Node -> [Hash -> SignedBlock \cup {NoBlock}]]
  /\ received \in [Node -> SUBSET SignedBlock]

Init ==
  /\ lastHash = NoHashVal
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]

\* The whole genesis block is broadcast to every ledger copy, not just one.
BroadcastGenesis(s) ==
  /\ Cardinality({n \in Node : ledger[n][s] # NoBlock}) = Cardinality(Node)
  \/ \A n \in Node : ledger[n] = [ledger[n] EXCEPT ![s] = [prev |-> NoHash, owner |-> s, kind |-> "genesis", target |-> s, amount |-> GenesisBalance]]

\* Ledger entry, sent-to-a-node set and last-hash are written in one breath.
WriteBlock(s, n, bl) ==
  /\ ledger' = [ledger EXCEPT ![n][s] = bl]
  /\ received' = [received EXCEPT ![n] = @ \cup {bl}]
  /\ lastHash' = s

CreateGenesis(b) ==
  /\ lastHash = NoHashVal
  /\ b \in PrivateKey
  /\ BroadcastGenesis(b)
  /\ lastHash' = CalculateHash([prev |-> NoHash, owner |-> b, kind |-> "genesis", target |-> b, amount |-> GenesisBalance], NoHashVal)
  /\ UNCHANGED <<ledger, received>>

\* Block creation is the only place the hash function is called, which is why
\* every hash generated here is locked into the chain forever.
CreateSend(n, b, rec, a) ==
  /\ b \in PrivateKey
  /\ lastHash # NoHashVal
  /\ BalanceOf(n, ledger[n], b) >= a
  /\ WriteBlock(CalculateHash([prev |-> lastHash, owner |-> b, kind |-> "send", target |-> rec, amount |-> a], lastHash), n,
        [prev |-> lastHash, owner |-> b, kind |-> "send", target |-> rec, amount |-> a])
  /\ UNCHANGED <<received>>

CreateOpen(n, b, h) ==
  /\ h \in Hash
  /\ ledger[n][h] # NoBlock
  /\ ledger[n][h].kind = "send"
  /\ ledger[n][h].target = b
  /\ BalanceOfOwner(n, ledger[n], b) = 0
  /\ lastHash # NoHashVal
  /\ WriteBlock(CalculateHash([prev |-> lastHash, owner |-> b, kind |-> "open", target |-> b, amount |-> 0], lastHash), n,
        [prev |-> lastHash, owner |-> b, kind |-> "open", target |-> b, amount |-> 0])
  /\ UNCHANGED <<received>>

CreateReceive(n, b, h) ==
  /\ h \in Hash
  /\ ledger[n][h] # NoBlock
  /\ ledger[n][h].kind = "send"
  /\ ledger[n][h].target = b
  /\ ~\E m \in Hash : ledger[n][m] # NoBlock /\ ledger[n][m].kind = "receive" /\ ledger[n][m].prev = h
  /\ lastHash # NoHashVal
  /\ WriteBlock(CalculateHash([prev |-> lastHash, owner |-> b, kind |-> "receive", target |-> b, amount |-> ledger[n][h].amount], lastHash), n,
        [prev |-> lastHash, owner |-> b, kind |-> "receive", target |-> b, amount |-> ledger[n][h].amount])
  /\ UNCHANGED <<received>>

CreateChange(n, b) ==
  /\ lastHash # NoHashVal
  /\ WriteBlock(CalculateHash([prev |-> lastHash, owner |-> b, kind |-> "change", target |-> b, amount |-> 0], lastHash), n,
        [prev |-> lastHash, owner |-> b, kind |-> "change", target |-> b, amount |-> 0])
  /\ UNCHANGED <<received>>

\* Validation reads the local copy and writes the copy and the received set
\* together, so validation can never be concurrently undone by another node.
Validate(n, bl) ==
  /\ bl \in received[n]
  /\ ledger[n][bl.prev] # NoBlock
  /\ ledger[n][bl.owner] = NoBlock
  /\ PublicKey[bl.owner] = bl.owner
  /\ \/ bl.kind \in {"open", "receive"} => BalanceOfOwner(n, ledger[n], bl.owner) = 0
     \/ bl.kind \in {"send", "receive"} => BalanceOf(n, ledger[n], bl.owner) >= bl.amount
  /\ ledger' = [ledger EXCEPT ![n][bl.prev] = bl]
  /\ received' = [received EXCEPT ![n] = @ \ {bl}]
  /\ UNCHANGED lastHash

Next ==
  \/ \E b \in PrivateKey : CreateGenesis(b)
  \/ \E n \in Node, b \in PrivateKey, rec \in PublicKey, a \in 1..GenesisBalance : CreateSend(n, b, rec, a)
  \/ \E n \in Node, b \in PublicKey, h \in Hash : CreateOpen(n, b, h)
  \/ \E n \in Node, b \in PublicKey, h \in Hash : CreateReceive(n, b, h)
  \/ \E n \in Node, b \in PrivateKey : CreateChange(n, b)
  \/ \E n \in Node, bl \in SignedBlock : Validate(n, bl)

Spec == Init /\ [][Next]_vars

BalanceOf(n, ledger, b, h) ==
  IF h \in Hash /\ ledger[h] # NoBlock
  THEN IF ledger[h].owner = b
       THEN IF ledger[h].kind = "receive" THEN ledger[h].amount + BalanceOf(n, ledger, b, ledger[h].prev)
            ELSE IF ledger[h].kind = "send" THEN BalanceOf(n, ledger, b, ledger[h].prev) - ledger[h].amount
            ELSE BalanceOf(n, ledger, b, ledger[h].prev)
       ELSE BalanceOf(n, ledger, b, ledger[h].prev)
  ELSE 0

BalanceOfOwner(n, ledger, b) == BalanceOf(n, ledger, b, lastHash)

\* Every block in every ledger copy must pass the signature check it needs.
SafetyInvariant ==
  \A n \in Node, h \in Hash : ledger[n][h] # NoBlock => PublicKey[ledger[n][h].owner] = ledger[n][h].owner

\* The total value across all accounts never exceeds what was minted.
BalanceConservation ==
  BalanceOfOwner(Node \in Node, ledger = ledger[CHOOSE n \in Node : TRUE], NoHashVal) <= GenesisBalance

====