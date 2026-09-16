"""Exact grammar-greedy selection with a conservative layout guard.

The grammar matcher remains authoritative for token acceptance.  Before a
candidate token is committed, this selector also checks the decoded response
text with the audited indentation-aware junction guard.  Rejected candidates
are never committed to the grammar matcher.  The guard is deliberately narrow
and carries no SANY or quality credit by itself.
"""
import operator

import torch

try:
    from layout_junction_audit import line_guard
except ModuleNotFoundError:
    from tools.layout_junction_audit import line_guard

try:
    from precedence_guard import precedence_guard
except ModuleNotFoundError:
    from tools.precedence_guard_audit import precedence_guard


class LayoutGuardDeadEnd(ValueError):
    """No finite token survives grammar plus both audited guards."""

    def __init__(self, steps, selected_token_ids, response_text):
        super().__init__("no finite layout-and-grammar-allowed token score")
        self.steps = int(steps)
        self.selected_token_ids = tuple(int(token) for token in selected_token_ids)
        self.response_text = response_text


class LayoutAwareGreedyGrammarSelector:
    def __init__(self, xgrammar, compiled_grammar, tokenizer, *, audit_steps=0,
                 response_text="", banned_token_ids_by_step=None):
        if isinstance(audit_steps, bool) or not isinstance(audit_steps, int) or audit_steps < 0:
            raise ValueError("audit_steps must be a nonnegative integer")
        if not callable(getattr(tokenizer, "decode", None)):
            raise ValueError("tokenizer with decode is required")
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
        self._tokenizer = tokenizer
        self._response_text = response_text
        self._piece_cache = {}
        banned = banned_token_ids_by_step or {}
        if not isinstance(banned, dict):
            raise ValueError("banned_token_ids_by_step must be a mapping")
        self._banned_token_ids_by_step = {}
        for step, token_ids in banned.items():
            if isinstance(step, bool) or not isinstance(step, int) or step < 0:
                raise ValueError("banned step must be a nonnegative integer")
            if not isinstance(token_ids, (set, frozenset, tuple, list)):
                raise ValueError("banned token IDs must be a finite collection")
            values = set()
            for token in token_ids:
                if isinstance(token, bool) or not isinstance(token, int):
                    raise ValueError("banned token ID must be an integer")
                if not 0 <= token < self._vocab_size:
                    raise ValueError("banned token ID outside vocabulary")
                values.add(token)
            self._banned_token_ids_by_step[step] = frozenset(values)

    def _piece(self, token):
        token = int(token)
        if token not in self._piece_cache:
            self._piece_cache[token] = self._tokenizer.decode(
                [token], skip_special_tokens=False,
                clean_up_tokenization_spaces=False)
        return self._piece_cache[token]

    def _layout_accepts(self, token):
        candidate = self._response_text + self._piece(token)
        return not line_guard(candidate) and not precedence_guard(candidate)

    def _reference_token(self, scores):
        bitmask = self._xgrammar.allocate_token_bitmask(1, self._vocab_size).cpu()
        self.matcher.fill_next_token_bitmask(bitmask)
        words = bitmask[0].to(dtype=torch.int64, device="cpu")
        shifts = torch.arange(32, dtype=torch.int64, device="cpu")
        allowed = ((words[:, None] >> shifts) & 1).bool().flatten()[: self._vocab_size]
        reference = scores[0].detach().cpu().masked_fill(~allowed, -torch.inf)
        # The ranked path applies the layout guard before grammar commitment.
        # The audit reference must use the identical candidate set; comparing
        # against grammar-only argmax would reject a valid layout-aware choice.
        ranked = torch.argsort(reference, descending=True, stable=True)
        for token in ranked.tolist():
            if not torch.isfinite(reference[token]).item():
                break
            if token in self._banned_token_ids_by_step.get(self.steps, ()):
                continue
            if self._layout_accepts(token):
                return int(token)
        raise LayoutGuardDeadEnd(self.steps, self.selected_token_ids,
                                 self._response_text)

    def __call__(self, input_ids, scores):
        if self._audit_failed:
            raise RuntimeError("selector unusable after audit mismatch")
        if (not isinstance(scores, torch.Tensor) or scores.ndim != 2 or
                scores.shape != (1, self._vocab_size) or
                not scores.is_floating_point() or scores.device.type not in ("cpu", "cuda")):
            raise ValueError("scores must be a floating CPU/CUDA tensor of shape [1, vocab_size]")
        if (not isinstance(input_ids, torch.Tensor) or input_ids.ndim != 2 or
                input_ids.shape[0] != 1 or input_ids.dtype not in (torch.int32, torch.int64) or
                input_ids.device.type not in ("cpu", "cuda")):
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
        ranked = torch.argsort(scores[0], descending=True, stable=True)
        for start in range(0, self._vocab_size, 64):
            chunk = ranked[start : start + 64]
            token_ids = chunk.tolist()
            values = scores[0].detach().index_select(0, chunk).tolist()
            for token, value in zip(token_ids, values):
                if value == -float("inf"):
                    break
                self.candidates_checked += 1
                if token in self._banned_token_ids_by_step.get(self.steps, ()):
                    continue
                if not self._layout_accepts(token):
                    continue
                if not self.matcher.accept_token(token):
                    continue
                if reference is not None and token != reference:
                    self._audit_failed = True
                    raise RuntimeError(
                        f"audit mismatch: ranked token {token}, dense token {reference}")
                result = torch.full_like(scores, -torch.inf)
                result[0, token] = scores[0, token]
                self._previous_input_ids = input_ids.detach().clone()
                self.selected_token_ids.append(token)
                self._response_text += self._piece(token)
                self.steps += 1
                if reference is not None:
                    self.audit_count += 1
                return result
            else:
                continue
            break
        if reference is not None:
            self._audit_failed = True
            raise RuntimeError("audit mismatch: no layout-and-grammar token")
        raise LayoutGuardDeadEnd(self.steps, self.selected_token_ids,
                                 self._response_text)

    def validate_generated(self, token_ids):
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
        if line_guard(self._response_text):
            raise ValueError("final response violates layout junction guard")
