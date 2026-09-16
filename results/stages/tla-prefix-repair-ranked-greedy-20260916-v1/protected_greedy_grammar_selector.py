"""Exact batch-one greedy selection; use as the last logits processor.

No model calls or full grammar masks outside the optional initial audits. Rank
search is bounded by the vocabulary, never by a heuristic candidate cutoff.
"""

import operator

import torch


class GreedyGrammarSelector:
    """Commit the highest finite-scoring token accepted by a fresh matcher.

    Only response tokens enter the matcher; the initial prompt is ignored.
    ``matcher`` is public for diagnostic-only, unmeasured prefix priming before
    the first call. Such priming is excluded from all counters and validation.
    Do not otherwise change matcher state or reuse a processor across responses.

    ``steps`` counts successful selections, ``candidates_checked`` counts actual
    accept_token attempts (including rejections), and ``audit_count`` counts
    successful dense comparisons. EOS is committed like any other token; the
    default XGrammar stop-token semantics then terminate the matcher.
    """

    def __init__(self, xgrammar, compiled_grammar, *, audit_steps=0):
        if isinstance(audit_steps, bool) or not isinstance(audit_steps, int) or audit_steps < 0:
            raise ValueError("audit_steps must be a nonnegative integer")
        self.matcher = xgrammar.GrammarMatcher(compiled_grammar)
        self.selected_token_ids = []
        self.candidates_checked = 0
        self.audit_count = 0
        self.steps = 0
        self._xgrammar = xgrammar
        self._vocab_size = compiled_grammar.tokenizer_info.vocab_size
        self._audit_steps = audit_steps
        self._previous_input_ids = None
        self._audit_failed = False

    def _reference_token(self, scores):
        # Fill on the very same matcher, before accepting ANY ranked candidate.
        bitmask = self._xgrammar.allocate_token_bitmask(1, self._vocab_size).cpu()
        self.matcher.fill_next_token_bitmask(bitmask)
        # XGrammar packs bit i into signed int32 word i//32. Shifting then
        # ANDing preserves bit 31 even when the word is negative; trim padding.
        words = bitmask[0].to(dtype=torch.int64, device="cpu")
        shifts = torch.arange(32, dtype=torch.int64, device="cpu")
        allowed = ((words[:, None] >> shifts) & 1).bool().flatten()[: self._vocab_size]
        reference = scores[0].detach().cpu().masked_fill(~allowed, -torch.inf)
        token = int(torch.argmax(reference).item())
        if not torch.isfinite(reference[token]).item():
            raise ValueError("no finite grammar-allowed token score")
        return token

    def __call__(self, input_ids, scores):
        if self._audit_failed:
            raise RuntimeError("selector unusable after audit mismatch")
        if (
            not isinstance(scores, torch.Tensor)
            or scores.ndim != 2
            or scores.shape != (1, self._vocab_size)
            or self._vocab_size == 0
            or not scores.is_floating_point()
            or scores.device.type not in ("cpu", "cuda")
        ):
            raise ValueError("scores must be a floating CPU/CUDA tensor of shape [1, vocab_size]")
        if (
            not isinstance(input_ids, torch.Tensor)
            or input_ids.ndim != 2
            or input_ids.shape[0] != 1
            or input_ids.dtype not in (torch.int32, torch.int64)
            or input_ids.device.type not in ("cpu", "cuda")
        ):
            raise ValueError("input_ids must be an integer CPU/CUDA tensor of shape [1, length]")
        previous = self._previous_input_ids
        if previous is not None:
            if input_ids.shape[1] != previous.shape[1] + 1:
                raise ValueError("input length must increment by exactly one")
            if int(input_ids[0, -1].item()) != self.selected_token_ids[-1]:
                raise ValueError("appended token differs from previous selected token")
            if not torch.equal(input_ids[:, :-1].to(previous.device), previous):
                raise ValueError("input prefix changed")
        if (torch.isnan(scores) | torch.isposinf(scores)).any().item():
            raise ValueError("scores contain NaN or positive infinity")
        if self.matcher.is_terminated():
            raise ValueError("grammar matcher has terminated after EOS")

        reference = self._reference_token(scores) if self.steps < self._audit_steps else None
        # Stable descending order preserves ascending token IDs within each tie,
        # exactly matching torch.argmax over a dense masked row.
        ranked = torch.argsort(scores[0], descending=True, stable=True)
        for start in range(0, self._vocab_size, 64):
            chunk = ranked[start : start + 64]
            token_ids = chunk.tolist()
            values = scores[0].detach().index_select(0, chunk).tolist()
            for token, value in zip(token_ids, values):
                if value == -float("inf"):
                    break
                self.candidates_checked += 1
                # XGrammar AcceptToken restores partial byte progress on false:
                # v0.2.2/v0.2.3 grammar_matcher.cc, AcceptToken, PopLastStates(pos).
                # Never rollback a rejection: that would undo an earlier token.
                if not self.matcher.accept_token(token):
                    continue
                if reference is not None and token != reference:
                    # Acceptance already committed, possibly EOS. Fail closed
                    # permanently instead of attempting to repair matcher state.
                    self._audit_failed = True
                    raise RuntimeError(
                        f"audit mismatch: ranked token {token}, dense token {reference}"
                    )
                result = torch.full_like(scores, -torch.inf)
                result[0, token] = scores[0, token]
                self._previous_input_ids = input_ids.detach().clone()
                self.selected_token_ids.append(token)
                self.steps += 1
                if reference is not None:
                    self.audit_count += 1
                return result
            else:
                continue
            break  # All remaining ranked scores are -inf.
        if reference is not None:
            self._audit_failed = True
            raise RuntimeError(f"audit mismatch: ranked search rejected dense token {reference}")
        raise ValueError("no finite grammar-allowed token score")

    def validate_generated(self, token_ids):
        """Require exact response IDs, including any selected EOS (no prompt).

        This verifies generation followed the processor, not grammar completion;
        a deliberately truncated or diagnostic one-step response can also match.
        """
        if self._audit_failed:
            raise RuntimeError("selector unusable after audit mismatch")
        if isinstance(token_ids, torch.Tensor):
            if token_ids.ndim != 1 or token_ids.dtype not in (torch.int32, torch.int64):
                raise ValueError("generated token_ids must be a one-dimensional integer sequence")
            token_ids = token_ids.tolist()
        try:
            actual = []
            for token in token_ids:
                if isinstance(token, bool):
                    raise TypeError("boolean token ID")
                actual.append(operator.index(token))
        except TypeError as exc:
            raise ValueError("generated token_ids must be an integer sequence") from exc
        if actual != self.selected_token_ids:
            raise ValueError("generated token IDs differ from selected_token_ids")
