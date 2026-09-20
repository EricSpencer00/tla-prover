# Intentionally Abstracted Away

1. **Producer and Consumer Identities**: The model does not track which specific producer or consumer performed each action. Multiple producers and consumers are modeled as non-deterministic choices to Produce or Consume. Only the effect on the shared buffer matters for safety verification.

2. **Item Content/Payload**: Actual data carried by items is abstracted away. Items are represented only by unique sequential IDs (1, 2, 3, ...). Safety depends only on item identity, ordering, and presence/absence—not on item content.

3. **Fairness and Liveness Properties**: The model does not guarantee eventual progress (e.g., producers eventually produce, consumers eventually consume). Fairness is a liveness property, not safety. Spec captures only safety: capacity is never violated, preconditions are checked, and FIFO order holds.

4. **Timeout and Blocking Semantics**: No wait/notify/condition variables or explicit thread blocking. When Produce or Consume cannot proceed, the model simply does not take that action; threads implicitly retry on the next step.

5. **Specific Buffer Implementation Details**: The underlying data structure (array, linked list, circular buffer) is abstracted. The model captures only FIFO append/remove-first semantics, which any correct implementation must preserve.

6. **Error Handling and Exceptions**: All operations succeed atomically. No error conditions, exceptions, or failure modes are modeled.

7. **Concurrency Granularity and Synchronization**: Entire Produce and Consume actions are atomic from the safety perspective. Internal synchronization mechanisms (locks, atomic instructions, memory fences) are not modeled—only their effect: mutual exclusion on the buffer.

8. **Resource Management**: No modeling of thread/process creation, destruction, lifecycle, or resource exhaustion.

9. **Multiple Instances or Pools**: The model captures one bounded buffer. Multiple independent buffers would require extending the state with additional variables.
