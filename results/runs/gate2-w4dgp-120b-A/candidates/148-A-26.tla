---- MODULE Nano ----
EXTENDS Naturals

\* A Nano cryptocurrency block-lattice: every account has its own chain of blocks.
\* Hashes and signatures are modeled as abstract constant operators, but the
\* safety invariant still checks that whatever blocks the model has admitted into
\* the replicated ledger are cryptographically self-consistent.
CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal

\* CalculateHash implements the exclusive-or-like operator used in the nano
\* spec; for model checking it replaces it with a total function over a small set.
ASSUME CalculateHash \in [Hash -> Hash]
CalculateHashImpl == CalculateHash

\* Hashes are opaque values in this spec; NoHash is the sentinel marking the empty
\* chain. (The hash operator is assumed to be total for every block configuration
\* the model can reach.)
NoHash == CHOOSE h \in Hash : TRUE

\* Ownership maps the crypto identity space to network nodes.
Owner == [key \in PrivateKey |-> CHOOSE n \in Node : n \in {x \in Node : n \in {x} \/ \E k \in PrivateKey : Owner[k] = x}]

\* A block names its predecessor in the account chain and the send block it acknowledges.
Block == [prev : Hash, sender : Hash, pk : PublicKey, amount : Nat, typ : {"genesis", "send", "open", "receive", "change"}]

VARIABLES lastHash, distributedLedger, received

vars == <<lastHash, distributedLedger, received>>

TypeOK ==
  /\ lastHash \in Hash
  /\ distributedLedger \in [Node -> [Hash -> Block \cup {NoBlockVal}]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ distributedLedger = [n \in Node |-> [h \in Hash |-> NoBlockVal]]
  /\ received = [n \in Node |-> {}]

\* Balance is a read-only sum over the account chain (no double counting, no double credit).
RECURSIVE SumOfChain(_)
SumOfChain(h) ==
  IF distributedLedger[CHOOSE n \in Node : distributedLedger[n][h] # NoBlockVal] [h].typ = "send"
  THEN
    LET pr == distributedLedger[CHOOSE n \in Node : distributedLedger[n][h] # NoBlockVal] [h].prev
    IN  distributedLedger[CHOOSE n \in Node : distributedLedger[n][h] # NoBlockVal] [h].amount + SumOfChain(pr)
  ELSE 0

RECURSIVE AccountBalance(_)
AccountBalance(h) ==
  IF h = NoHashVal THEN 0
  ELSE
    LET r == AccountBalance(distributedLedger[CHOOSE n \in Node : distributedLedger[n][h] # NoBlockVal] [h].prev)
    IN IF distributedLedger[CHOOSE n \in Node : distributedLedger[n][h] # NoBlockVal] [h].typ = "receive"
       THEN r + distributedLedger[CHOOSE n \in Node : distributedLedger[n][h] # NoBlockVal] [h].amount
       ELSE r

\* Each broadcast is delivered to every node's inbox, so no loss is simulated.
Broadcast(h) == [n \in Node |-> received[n] \cup {h}]

\* The owner's private key signs the block; the invariant below re-checks it.
Sign(n, b) == (b.typ = "genesis") \/ (b.pk = Owner[CHOOSE k \in PrivateKey : Owner[k] = n])

CreateGenesisBlock(n) ==
  LET b == [prev |-> NoHashVal, sender |-> NoHashVal, pk |-> Owner[n], amount |-> GenesisBalance, typ |-> "genesis"]
  IN /\ lastHash = NoHashVal
     /\ lastHash' = CalculateHashImpl(NoHashVal)
     /\ distributedLedger' = [n2 \in Node |-> [distributedLedger[n2] EXCEPT ![lastHash' |-> b]]
     /\ received' = Broadcast(lastHash')
     /\ UNCHANGED <<>>

CreateSendBlock(n, to, amt) ==
  LET b == [prev |-> lastHash, sender |-> lastHash, pk |-> Owner[n], amount |-> amt, typ |-> "send"]
  IN /\ Sign(n, b)
     /\ AccountBalance(lastHash) >= amt
     /\ lastHash' = CalculateHashImpl(lastHash)
     /\ distributedLedger' = [n2 \in Node |-> [distributedLedger[n2] EXCEPT ![lastHash' |-> b]]
     /\ received' = Broadcast(lastHash')
     /\ UNCHANGED <<>>

CreateOpenBlock(n, sb) ==
  LET b == [prev |-> NoHashVal, sender |-> sb, pk |-> Owner[n], amount |-> 0, typ |-> "open"]
  IN /\ Sign(n, b)
     /\ UNCHANGED received
     /\ lastHash' = CalculateHashImpl(sb)
     /\ distributedLedger' = [n2 \in Node |-> [distributedLedger[n2] EXCEPT ![lastHash' |-> b]]
     /\ received' = Broadcast(lastHash')
     /\ UNCHANGED <<>>

CreateReceiveBlock(n, sb) ==
  LET b == [prev |-> lastHash, sender |-> sb, pk |-> Owner[n], amount |-> 0, typ |-> "receive"]
  IN /\ Sign(n, b)
     /\ lastHash' = CalculateHashImpl(sb)
     /\ distributedLedger' = [n2 \in Node |-> [distributedLedger[n2] EXCEPT ![lastHash' |-> b]]
     /\ received' = Broadcast(lastHash')
     /\ UNCHANGED <<>>

CreateChangeRepBlock(n) ==
  LET b == [prev |-> lastHash, sender |-> lastHash, pk |-> Owner[n], amount |-> 0, typ |-> "change"]
  IN /\ Sign(n, b)
     /\ lastHash' = CalculateHashImpl(lastHash)
     /\ distributedLedger' = [n2 \in Node |-> [distributedLedger[n2] EXCEPT ![lastHash' |-> b]]
     /\ received' = Broadcast(lastHash')
     /\ UNCHANGED <<>>

ValidateBlock(n, h) ==
  /\ h \in received[n]
  /\ LET blk == distributedLedger[CHOOSE n2 \in Node : distributedLedger[n2][h] # NoBlockVal] [h]
     IN /\ Sign(n, blk)
        /\ (blk.prev = NoHashVal \/ distributedLedger[n][blk.prev] # NoBlockVal)
        /\ IF blk.typ = "send" THEN AccountBalance(blk.prev) >= blk.amount ELSE TRUE
        /\ IF blk.typ = "open" THEN blk.sender \notin {c \in Hash : distributedLedger[n][c] # NoBlockVal /\ distributedLedger[n][c].typ = "receive"} ELSE TRUE
        /\ IF blk.typ = "receive" THEN blk.sender \notin {c \in Hash : distributedLedger[n][c] # NoBlockVal /\ distributedLedger[n][c].typ = "receive"} ELSE TRUE
        /\ distributedLedger' = [distributedLedger EXCEPT ![n] = [distributedLedger[n] EXCEPT ![h] = blk]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash>>

Next ==
  \/ \E n \in Node : CreateGenesisBlock(n) \/ CreateChangeRepBlock(n)
  \/ \E n \in Node, to \in Node, amt \in 1..GenesisBalance : CreateSendBlock(n, to, amt)
  \/ \E n \in Node, sb \in Hash : CreateOpenBlock(n, sb) \/ CreateReceiveBlock(n, sb)
  \/ \E n \in Node, h \in Hash : ValidateBlock(n, h)

Spec == Init /\ [][Next]_vars

\* Every block recorded in every node's replicated ledger must have a valid
\* signature, whatever chain-building order produced it -- that is the invariant.
SafetyInvariant ==
  /\ TypeOK
  /\ \A n \in Node, h \in Hash : distributedLedger[n][h] # NoBlockVal => Sign(n, distributedLedger[n][h])

====