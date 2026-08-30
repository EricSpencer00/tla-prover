---- MODULE Nano ----
EXTENDS Naturals, Sequences

CONSTANTS
  Hash, NoHashVal, PrivateKey, PublicKey, Node, GenesisBalance, NoBlockVal, CalculateHash, NoHash, NoBlock

\* Every account's chain of blocks is stored as a sequence keyed by that account's
\* public key; each block has a type and a signed payload, and its hash is the key
\* under which it is stored in the replicated ledger.
Block == [type: {"genesis", "send", "open", "receive", "change"}, src: PublicKey,
          dst: PublicKey, amt: Nat, prev: Hash, sig: PrivateKey]
Chain == Seq(Block)
TxLog == [Node -> Chain]
Ledger == [Hash -> Block \cup NoBlockVal]

\* The sum of the last block of each account chain's amounts is the chain's balance.
ChainBalance(ch) == LET f[i \in 1..Len(ch)] ==
  (IF ch[i].type = "send" THEN -ch[i].amt
   ELSE IF ch[i].type \in {"open", "receive"} THEN ch[i].amt
   ELSE 0) * 1
  IN LET g[i \in 0..Len(ch)] == IF i = 0 THEN 0 ELSE g[i-1] + f[i] IN g[Len(ch)]

RECURSIVE SumOfChains(_)
SumOfChains(S) ==
  IF S = {} THEN 0
  ELSE LET a == CHOOSE x \in S : TRUE IN ChainBalance(TxLog[a]) + SumOfChains(S \ {a})

VARIABLES lastHash, ledger, received, TxLog

vars == <<lastHash, ledger, received, TxLog>>

TypeOK ==
  /\ lastHash \in Hash \cup NoHashVal
  /\ ledger \in [Node -> Ledger]
  /\ received \in [Node -> SUBSET Hash]
  /\ TxLog \in [PublicKey -> Chain]

Init ==
  /\ lastHash = NoHash
  /\ ledger = [n \in Node |-> [h \in Hash |-> NoBlock]]
  /\ received = [n \in Node |-> {}]
  /\ TxLog = [pk \in PublicKey |-> << >>]

Broadcast(n, h) ==
  /\ h \notin received[n]
  /\ received' = [received EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED <<lastHash, ledger, TxLog>>

Validate(n, h) ==
  /\ h \in received[n]
  /\ ledger[n][h] = NoBlock
  /\ ledger' = [ledger EXCEPT ![n][h] = ledger[NoHash][h]]
  /\ received' = [received EXCEPT ![n] = @ \ {h}]
  /\ UNCHANGED <<lastHash, TxLog>>

ValidateAny(n) == \E h \in Hash : Validate(n, h)

BroadcastAny == \E n \in Node, h \in Hash : Broadcast(n, h)

Next ==
  \/ BroadcastAny
  \/ \E n \in Node : ValidateAny(n)

\* Genesis (only once): the whole supply is placed on one account's chain.
CreateGenesisBlock ==
  /\ lastHash = NoHash
  /\ \E n \in Node, pk \in PrivateKey, pb \in PublicKey :
       /\ ledger[NoHash][NoHash] = NoBlock
       /\ LET h == CalculateHash(n @@ "genesis" @@ pb @@ NoHash) IN
            /\ lastHash' = h
            /\ ledger' = [ledger EXCEPT ![NoHash][NoHash] =
                             [type |-> "genesis", src |-> pb, dst |-> pb, amt |-> GenesisBalance,
                              prev |-> NoHash, sig |-> pk]]
            /\ TxLog' = [TxLog EXCEPT ![pb] = Append(TxLog[pb],
                             [type |-> "genesis", src |-> pb, dst |-> pb, amt |-> GenesisBalance,
                              prev |-> NoHash, sig |-> pk])]
            /\ received' = [n \in Node |-> IF n = NoHash THEN {h} ELSE {}]
  \/ UNCHANGED vars

CreateSendBlock ==
  /\ \E n \in Node, src \in PublicKey, dst \in PublicKey, pk \in PrivateKey :
       /\ ledger[n][NoHash] # NoBlock
       /\ LET srcch == TxLog[src] IN
            /\ srcch # << >>
            /\ ledger[n][srcch[Len(srcch)].prev] # NoBlock
            /\ \E amt \in 1..GenesisBalance :
                 /\ SumOfChains(Domains(TxLog)) + amt <= GenesisBalance
                 /\ LET h == CalculateHash(n @@ "send" @@ src @@ dst @@ amt @@ srcch[Len(srcch)].prev)
                        blk == [type |-> "send", src |-> src, dst |-> dst, amt |-> amt,
                                prev |-> srcch[Len(srcch)].prev, sig |-> pk]
                     IN /\ ledger' = [ledger EXCEPT ![n][srcch[Len(srcch)].prev] = blk]
                        /\ TxLog' = [TxLog EXCEPT ![src] = Append(srcch, blk)]
                        /\ lastHash' = h
                        /\ received' = [received EXCEPT ![n] = @ \cup {h}]
  \/ UNCHANGED vars

CreateOpenBlock ==
  /\ \E n \in Node, pk \in PrivateKey, dst \in PublicKey :
       /\ ledger[n][NoHash] # NoBlock
       /\ TxLog[dst] = << >>
       /\ \E src \in PublicKey :
            /\ \E amt \in 1..GenesisBalance :
                 LET srcch == TxLog[src] IN
                  /\ srcch # << >>
                  /\ srcch[Len(srcch)].type = "send"
                  /\ srcch[Len(srcch)].dst = dst
                  /\ srcch[Len(srcch)].amt = amt
                  /\ ledger[n][srcch[Len(srcch)].prev] # NoBlock
                  /\ LET h == CalculateHash(n @@ "open" @@ src @@ dst @@ amt @@ srcch[Len(srcch)].prev)
                         blk == [type |-> "open", src |-> src, dst |-> dst, amt |-> amt,
                                 prev |-> srcch[Len(srcch)].prev, sig |-> pk]
                     IN /\ ledger' = [ledger EXCEPT ![n][srcch[Len(srcch)].prev] = blk]
                        /\ TxLog' = [TxLog EXCEPT ![dst] = Append(TxLog[dst], blk)]
                        /\ lastHash' = h
                        /\ received' = [received EXCEPT ![n] = @ \cup {h}]
  \/ UNCHANGED vars

CreateReceiveBlock ==
  /\ \E n \in Node, dst \in PublicKey, pk \in PrivateKey :
       /\ TxLog[dst] # << >>
       /\ \E src \in PublicKey :
            /\ \E amt \in 1..GenesisBalance :
                 LET srcch == TxLog[src] IN
                  /\ srcch # << >>
                  /\ srcch[Len(srcch)].type = "send"
                  /\ srcch[Len(srcch)].dst = dst
                  /\ srcch[Len(srcch)].amt = amt
                  /\ ledger[n][srcch[Len(srcch)].prev] # NoBlock
                  /\ \A b \in TxLog[dst] : b.type # "receive" \/ b.prev # srcch[Len(srcch)].prev
                  /\ LET h == CalculateHash(n @@ "receive" @@ src @@ dst @@ amt @@ srcch[Len(srcch)].prev)
                         blk == [type |-> "receive", src |-> src, dst |-> dst, amt |-> amt,
                                 prev |-> srcch[Len(srcch)].prev, sig |-> pk]
                     IN /\ ledger' = [ledger EXCEPT ![n][srcch[Len(srcch)].prev] = blk]
                        /\ TxLog' = [TxLog EXCEPT ![dst] = Append(TxLog[dst], blk)]
                        /\ lastHash' = h
                        /\ received' = [received EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED vars

CreateChangeRepresentative ==
  /\ \E n \in Node, pk \in PrivateKey, dst \in PublicKey :
       /\ \E ch \in Chain : \E p \in PublicKey :
            /\ ch # << >>
            /\ ledger[n][ch[Len(ch)].prev] # NoBlock
            /\ LET h == CalculateHash(n @@ "change" @@ dst @@ ch[Len(ch)].amt @@ ch[Len(ch)].prev)
                   blk == [type |-> "change", src |-> dst, dst |-> dst, amt |-> ch[Len(ch)].amt,
                           prev |-> ch[Len(ch)].prev, sig |-> pk]
               IN /\ ledger' = [ledger EXCEPT ![n][ch[Len(ch)].prev] = blk]
                  /\ TxLog' = [TxLog EXCEPT ![dst] = Append(ch, blk)]
                  /\ lastHash' = h
                  /\ received' = [received EXCEPT ![n] = @ \cup {h}]
  /\ UNCHANGED vars

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A n \in Node : WF_vars(ValidateAny(n))

\* Every block in every node's ledger must be signed by the account key that
\* owns the chain it lives in; that excludes tampered or forged entries.
SafetyInvariant == \A n \in Node : \A h \in Hash, i \in 1..Len(TxLog[TxLog[n][h].src]) :
  TxLog[n][TxLog[TxLog[n][h].src].src][i].sig = TxLog[n][TxLog[n][h].src].src

====