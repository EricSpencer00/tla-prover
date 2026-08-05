---- MODULE Nano ----
EXTENDS Naturals, FiniteSets, TLC

\* A Nano-like block-lattice: every account has its own chain of blocks, so
\* the order in which actions happened is baked into the data structure.
\* The model focuses on hash and signature correctness, not on chain ordering.
CONSTANTS Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, NoHash, CalculateHash

PublicKeyOf == [k \in PrivateKey |-> CHOOSE p \in PublicKey : p \in PublicKey : p = k]
OwnerOf == [n \in Node |-> PublicKeyOf[n]]
NoBlock == CHOOSE b \in Hash : b \notin Hash

VARIABLES lastHash, distributedLedger, received

RECURSIVE chainBalances(_)
chainBalances(b) ==
  IF b = NoHash
  THEN 0
  ELSE LET blk == distributedLedger[b] IN
       IF blk.type = "send"
       THEN chainBalances(blk.prev) - blk.amount
       ELSE IF blk.type = "receive"
       THEN chainBalances(blk.prev) + blk.amount
       ELSE chainBalances(blk.prev)

RECURSIVE accountBalance(_, _)
accountBalance(h, p) ==
  IF h = NoHash
  THEN 0
  ELSE LET blk == distributedLedger[h] IN
       IF blk.source = p
       THEN chainBalances(h)
       ELSE accountBalance(blk.prev, p)

BalanceOf(p) == accountBalance(lastHash, p)

CommittedBlocks == {b \in Hash : distributedLedger[b] # NoBlockVal}

TypeOK ==
  /\ lastHash \in Hash \cup {NoHashVal}
  /\ distributedLedger \in [Hash -> [type: {"genesis", "send", "open", "receive", "change"}, source: PublicKey, dest: PublicKey, amount: Nat, signature: PrivateKey, prev: Hash]]
  /\ received \in [Node -> SUBSET Hash]

Init ==
  /\ lastHash = NoHashVal
  /\ distributedLedger = [h \in Hash |-> NoBlockVal]
  /\ received = [n \in Node |-> {}]

\* Genesis block created once; it funds the entire supply into one account.
CreateGenesis(n) ==
  /\ lastHash = NoHashVal
  /\ ~DistributedLedger[NoHashVal]
  /\ LET h == CalculateHash([type |-> "genesis", source |-> OwnerOf[n], dest |-> OwnerOf[n], amount |-> GenesisBalance, prev |-> NoHashVal]) IN
     lastHash' = h /\ distributedLedger' = [distributedLedger EXCEPT ![h] = [type |-> "genesis", source |-> OwnerOf[n], dest |-> OwnerOf[n], amount |-> GenesisBalance, signature |-> n, prev |-> NoHashVal]]
  /\ UNCHANGED received

\* Normal send block: withdraws from the sender's own chain.
CreateSend(n, to, amt) ==
  /\ LastHash \in Hash
  /\ amt > 0
  /\ amt <= accountBalance(LastHash, OwnerOf[n])
  /\ LET h == CalculateHash([type |-> "send", source |-> OwnerOf[n], dest |-> to, amount |-> amt, prev |-> LastHash]) IN
     lastHash' = h /\ distributedLedger' = [distributedLedger EXCEPT ![h] = [type |-> "send", source |-> OwnerOf[n], dest |-> to, amount |-> amt, signature |-> n, prev |-> LastHash]]
  /\ received' = [n \in Node |-> received[n] \cup {h}]

CreateOpen(n, ref) ==
  /\ ref \in CommittedBlocks
  /\ distributedLedger[ref].dest = OwnerOf[n]
  /\ ~\E h \in CommittedBlocks : distributedLedger[h].source = OwnerOf[n]
  /\ LET h == CalculateHash([type |-> "open", source |-> OwnerOf[n], dest |-> OwnerOf[n], amount |-> 0, prev |-> ref]) IN
     lastHash' = h /\ distributedLedger' = [distributedLedger EXCEPT ![h] = [type |-> "open", source |-> OwnerOf[n], dest |-> OwnerOf[n], amount |-> 0, signature |-> n, prev |-> ref]]
  /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateReceive(n, sendRef) ==
  /\ sendRef \in CommittedBlocks
  /\ distributedLedger[sendRef].dest = OwnerOf[n]
  /\ ~\E h \in CommittedBlocks : distributedLedger[h].type = "receive" /\ distributedLedger[h].prev = sendRef
  /\ LastHash \in Hash
  /\ LET h == CalculateHash([type |-> "receive", source |-> OwnerOf[n], dest |-> OwnerOf[n], amount |-> 0, prev |-> sendRef]) IN
     lastHash' = h /\ distributedLedger' = [distributedLedger EXCEPT ![h] = [type |-> "receive", source |-> OwnerOf[n], dest |-> OwnerOf[n], amount |-> 0, signature |-> n, prev |-> sendRef]]
  /\ received' = [m \in Node |-> received[m] \cup {h}]

CreateChange(n, newRep) ==
  /\ LastHash \in Hash
  /\ LET h == CalculateHash([type |-> "change", source |-> OwnerOf[n], dest |-> newRep, amount |-> 0, prev |-> LastHash]) IN
     lastHash' = h /\ distributedLedger' = [distributedLedger EXCEPT ![h] = [type |-> "change", source |-> OwnerOf[n], dest |-> newRep, amount |-> 0, signature |-> n, prev |-> LastHash]]
  /\ received' = [m \in Node |-> received[m] \cup {h}]

Next ==
  \/ \E n \in Node : CreateGenesis(n)
  \/ \E n \in Node, to \in PublicKey, amt \in Nat : CreateSend(n, to, amt)
  \/ \E n \in Node, ref \in Hash : CreateOpen(n, ref)
  \/ \E n \in Node, sendRef \in Hash : CreateReceive(n, sendRef)
  \/ \E n \in Node, newRep \in PublicKey : CreateChange(n, newRep)

Spec == Init /\ [][Next]_<<lastHash, distributedLedger, received>>

\* Every block in every node's ledger has a signature that matches the
\* public key of the account that owns the chain this block sits in.
SignatureMatchesOwner ==
  \A h \in Hash : distributedLedger[h] # NoBlockVal => PublicKeyOf[distributedLedger[h].signature] = distributedLedger[h].source
====