MODULE BoundedBuffer

(*
  Minimal TLA+ model of a bounded FIFO buffer shared by multiple producers and consumers.

  Safety-relevant state:
  - Current buffer contents (sequence of items identified by unique IDs)
  - Counter for producing unique item identifiers

  Safety properties modeled:
  1. Buffer capacity is never exceeded
  2. Producers can only produce when buffer is not full
  3. Consumers can only consume when buffer is not empty
  4. Items are consumed in FIFO order
  5. No data loss or spurious item duplication

  Intentional abstractions: see ABSTRACTED.md
*)

CONSTANT CAPACITY  (* Maximum number of items in buffer *)

VARIABLE
  buffer,       (* Sequence of items currently in buffer *)
  next_item_id  (* Next unique identifier for items to produce *)

vars == <<buffer, next_item_id>>

(*
  Type invariant: buffer is a sequence of item IDs (natural numbers),
  each less than next_item_id. Buffer length is bounded by CAPACITY.
*)
TypeOK ==
  /\ buffer \in Seq(Nat)
  /\ next_item_id \in Nat
  /\ Len(buffer) <= CAPACITY
  /\ \A i \in 1..Len(buffer): buffer[i] < next_item_id

Init ==
  /\ buffer = << >>
  /\ next_item_id = 1

(*
  Producer action: append item to buffer if space available.
  Each produced item gets a unique increasing ID.
*)
Produce ==
  /\ Len(buffer) < CAPACITY
  /\ buffer' = Append(buffer, next_item_id)
  /\ next_item_id' = next_item_id + 1

(*
  Consumer action: remove item from buffer if available.
  Items are removed in FIFO order (from front).
*)
Consume ==
  /\ Len(buffer) > 0
  /\ buffer' = Tail(buffer)
  /\ UNCHANGED next_item_id

Next == Produce \/ Consume

Spec == Init /\ [][Next]_vars

(*
  Safety Invariants
*)

(* No buffer overflow: length never exceeds capacity *)
SafeCapacity == Len(buffer) <= CAPACITY

(* All items in buffer are valid: have been produced (ID < next_item_id) *)
ValidItems == \A i \in 1..Len(buffer): buffer[i] < next_item_id

(*
  FIFO order: items are in strictly increasing order of production.
  This follows from append-to-end and remove-from-front semantics.
*)
FIFOOrder == \A i, j \in 1..Len(buffer): i < j => buffer[i] < buffer[j]

(* No duplicate items in buffer: each item ID appears at most once *)
NoDuplicates == \A i, j \in 1..Len(buffer): i /= j => buffer[i] /= buffer[j]
