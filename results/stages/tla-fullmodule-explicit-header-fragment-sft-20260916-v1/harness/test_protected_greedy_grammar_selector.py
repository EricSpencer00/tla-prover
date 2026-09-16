"""Local synthetic-vocabulary controls; no model or tokenizer downloads."""

import pytest

torch = pytest.importorskip("torch")
xgr = pytest.importorskip("xgrammar")

from tools.protected_greedy_grammar_selector import GreedyGrammarSelector


def compile_grammar(vocab, grammar='root ::= "ab"'):
    info = xgr.TokenizerInfo(vocab, stop_token_ids=[len(vocab) - 1])
    return xgr.GrammarCompiler(info, max_threads=1).compile_grammar(grammar)


@pytest.fixture
def compiled():
    # "ax" partially matches before rejection, exercising internal rollback.
    return compile_grammar(["ax", "a", "b", "ab", "x", "<eos>"])


def dense_token(matcher, scores):
    bitmask = xgr.allocate_token_bitmask(1, scores.shape[1])
    matcher.fill_next_token_bitmask(bitmask)
    # Independent scalar unpacking in tests, not the selector's vectorized path.
    words = bitmask[0].tolist()
    allowed = torch.tensor(
        [bool((words[i // 32] >> (i % 32)) & 1) for i in range(scores.shape[1])]
    )
    masked = scores.detach().cpu().masked_fill(~allowed[None, :], -torch.inf)
    selected = int(masked.argmax().item())
    assert torch.isfinite(masked[0, selected])
    return selected


def test_first_subsequent_rejections_and_eos(compiled):
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=3)
    prompt = torch.tensor([[4, 4]])  # Would be invalid if passed to the matcher.
    scores = torch.tensor([[10.0, 9.0, 8.0, 7.0, 6.0, 11.0]])
    original = scores.clone()
    independent = xgr.GrammarMatcher(compiled)
    for expected in [1, 2, 5]:
        assert dense_token(independent, scores) == expected
        result = selector(prompt, scores)
        assert result.shape == scores.shape
        assert result.argmax().item() == expected
        assert torch.isfinite(result).sum().item() == 1
        assert result[0, expected] == scores[0, expected]
        assert torch.equal(scores, original)
        assert independent.accept_token(expected)
        prompt = torch.cat([prompt, torch.tensor([[expected]])], dim=1)
        if expected == 2:
            assert not selector.matcher.is_terminated()
    assert selector.matcher.is_terminated()
    assert selector.selected_token_ids == [1, 2, 5]
    assert (selector.steps, selector.audit_count, selector.candidates_checked) == (3, 3, 8)
    selector.validate_generated([1, 2, 5])
    selector.validate_generated(torch.tensor([1, 2, 5]))
    with pytest.raises(ValueError, match="terminated"):
        selector(prompt, scores)


@pytest.mark.parametrize("audit_steps", [0, 1])
def test_no_rank_cap_and_no_mask_outside_audit(monkeypatch, audit_steps):
    compiled = compile_grammar(["ax"] * 193 + ["ab", "<eos>"])
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=audit_steps)
    fill = selector.matcher.fill_next_token_bitmask
    accept = selector.matcher.accept_token
    events = []

    def tracked_fill(mask):
        events.append("mask")
        assert audit_steps, "dense mask used outside audit"
        return fill(mask)

    def tracked_accept(token):
        events.append(token)
        return accept(token)

    monkeypatch.setattr(selector.matcher, "fill_next_token_bitmask", tracked_fill)
    monkeypatch.setattr(selector.matcher, "accept_token", tracked_accept)
    if not audit_steps:
        def forbidden_allocate(*args):
            pytest.fail("allocated a full grammar mask without audit")
        monkeypatch.setattr(xgr, "allocate_token_bitmask", forbidden_allocate)
    scores = torch.arange(195, 0, -1, dtype=torch.float32)[None, :]
    assert selector(torch.empty((1, 0), dtype=torch.long), scores).argmax().item() == 193
    assert selector.candidates_checked == 194
    assert events == (["mask"] if audit_steps else []) + list(range(194))
    assert selector.audit_count == audit_steps


@pytest.mark.parametrize("audit_steps", [0, 1])
@pytest.mark.parametrize("dtype", [torch.float16, torch.bfloat16, torch.float32, torch.float64])
def test_ties_and_noncontiguous_scores(compiled, audit_steps, dtype):
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=audit_steps)
    backing = torch.zeros((1, 12), dtype=dtype)
    scores = backing[:, ::2]
    scores[0, 1] = -0.0
    expected = dense_token(xgr.GrammarMatcher(compiled), scores)
    result = selector(torch.tensor([[4]]), scores)
    assert expected == result.argmax().item() == 1
    assert result.dtype == dtype and result.device == scores.device
    assert result.data_ptr() != scores.data_ptr()
    assert torch.signbit(result[0, 1])
    assert torch.count_nonzero(backing) == 0


@pytest.mark.parametrize("valid_id", [31, 32, 63, 64, 96])
def test_audit_signed_words_and_vocabulary_padding(valid_id):
    vocab = ["x"] * 98
    vocab[valid_id] = "ab"
    vocab[-1] = "<eos>"
    selector = GreedyGrammarSelector(xgr, compile_grammar(vocab), audit_steps=1)
    scores = torch.zeros((1, len(vocab)))
    assert selector(torch.tensor([[0]]), scores).argmax().item() == valid_id
    assert selector.audit_count == 1


def test_audit_only_initial_steps(compiled, monkeypatch):
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=1)
    scores = torch.tensor([[9.0, 8.0, 7.0, 6.0, 5.0, 4.0]])
    selector(torch.tensor([[4]]), scores)

    def forbidden_fill(*args):
        pytest.fail("audit exceeded its initial step budget")

    monkeypatch.setattr(selector.matcher, "fill_next_token_bitmask", forbidden_fill)
    selector(torch.tensor([[4, 1]]), scores)
    selector(torch.tensor([[4, 1, 2]]), scores)
    assert (selector.steps, selector.audit_count) == (3, 1)


def test_diagnostic_priming_and_fresh_matcher(compiled):
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=1)
    fresh = GreedyGrammarSelector(xgr, compiled)
    independent = xgr.GrammarMatcher(compiled)
    assert selector.matcher is not fresh.matcher
    assert selector.matcher.accept_token(1)
    assert independent.accept_token(1)
    scores = torch.tensor([[9.0, 8.0, 7.0, 6.0, 5.0, 4.0]])
    expected = dense_token(independent, scores)
    selected = selector(torch.tensor([[4, 4]]), scores).argmax().item()
    assert selected == expected == 2
    selector.validate_generated([selected])
    assert (selector.steps, selector.audit_count, selector.candidates_checked) == (1, 1, 3)
    assert fresh(torch.tensor([[4]]), scores).argmax().item() == 1


@pytest.mark.parametrize("audit_steps", [0, 1])
@pytest.mark.parametrize("finite_invalid", [False, True])
def test_no_finite_allowed_token(compiled, audit_steps, finite_invalid):
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=audit_steps)
    scores = torch.full((1, 6), -torch.inf)
    if finite_invalid:
        scores[0, 0] = 10  # Partial match then rejection; valid tokens are -inf.
    with pytest.raises(ValueError, match="no finite grammar-allowed"):
        selector(torch.tensor([[4]]), scores)
    assert selector.selected_token_ids == [] and selector.steps == selector.audit_count == 0
    assert selector.candidates_checked == int(finite_invalid and not audit_steps)
    assert selector.matcher.accept_token(3)  # Failure left the matcher at its original state.


@pytest.mark.parametrize("audit_steps", [0, 1])
@pytest.mark.parametrize("bad", [float("nan"), float("inf")])
@pytest.mark.parametrize("token", [0, 1])
def test_nan_and_positive_infinity_fail_before_acceptance(compiled, audit_steps, bad, token):
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=audit_steps)
    scores = torch.zeros((1, 6))
    scores[0, token] = bad
    with pytest.raises(ValueError, match="NaN or positive infinity"):
        selector(torch.tensor([[4]]), scores)
    assert selector.steps == selector.audit_count == selector.candidates_checked == 0
    assert selector.matcher.accept_token(3)


@pytest.mark.parametrize("scores", [
    torch.zeros(6), torch.zeros((2, 6)), torch.zeros((1, 5)),
    torch.zeros((1, 0)), torch.zeros((1, 6), dtype=torch.long), [[0.0] * 6],
])
def test_malformed_scores(compiled, scores):
    selector = GreedyGrammarSelector(xgr, compiled)
    with pytest.raises(ValueError, match="scores must"):
        selector(torch.tensor([[4]]), scores)
    assert selector.candidates_checked == 0


@pytest.mark.parametrize("ids", [
    torch.tensor([4]), torch.tensor([[4], [4]]), torch.tensor([[4.0]]), [[4]],
])
def test_malformed_input_batch(compiled, ids):
    selector = GreedyGrammarSelector(xgr, compiled)
    with pytest.raises(ValueError, match="input_ids must"):
        selector(ids, torch.zeros((1, 6)))
    assert selector.candidates_checked == 0


@pytest.mark.parametrize("ids, message", [
    ([[4, 4]], "increment"), ([[4, 4, 1, 2]], "increment"),
    ([[4]], "increment"), ([[4, 4, 3]], "appended token"),
    ([[0, 4, 1]], "prefix changed"),
])
def test_prefix_protocol(compiled, ids, message):
    selector = GreedyGrammarSelector(xgr, compiled)
    prompt = torch.tensor([[4, 4]])
    scores = torch.zeros((1, 6))
    selector(prompt, scores)
    prompt[0, 0] = 0  # The selector must hold its own snapshot.
    checked = selector.candidates_checked
    with pytest.raises(ValueError, match=message):
        selector(torch.tensor(ids), scores)
    assert selector.candidates_checked == checked
    assert selector(torch.tensor([[4, 4, 1]]), scores).argmax().item() == 2


@pytest.mark.parametrize("tokens", [[], [3], [1, 2], [4, 1], [1.0], [True], [[1]]])
def test_generated_must_match_exactly(compiled, tokens):
    selector = GreedyGrammarSelector(xgr, compiled)
    selector(torch.tensor([[4]]), torch.zeros((1, 6)))
    with pytest.raises(ValueError, match="generated token"):
        selector.validate_generated(tokens)


@pytest.mark.parametrize("reject_all", [False, True])
def test_audit_mismatch_fails_closed(compiled, monkeypatch, reject_all):
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=1)
    accept = selector.matcher.accept_token
    # Deliberately corrupt candidate acceptance while keeping the real dense
    # reference: reject its winner, then either accept a lower rank or none.
    monkeypatch.setattr(
        selector.matcher, "accept_token",
        lambda token: False if reject_all or token == 1 else accept(token),
    )
    with pytest.raises(RuntimeError, match="audit mismatch"):
        selector(torch.tensor([[4]]), torch.zeros((1, 6)))
    assert selector.steps == selector.audit_count == 0
    with pytest.raises(RuntimeError, match="unusable"):
        selector(torch.tensor([[4]]), torch.zeros((1, 6)))
    with pytest.raises(RuntimeError, match="unusable"):
        selector.validate_generated([])


@pytest.mark.parametrize("audit_steps", [-1, 1.5, True])
def test_invalid_audit_budget(compiled, audit_steps):
    with pytest.raises(ValueError, match="audit_steps"):
        GreedyGrammarSelector(xgr, compiled, audit_steps=audit_steps)


@pytest.mark.parametrize("audit_steps", [0, 8])
def test_seeded_multistep_dense_differential(audit_steps):
    vocab = ["ax", "a", "b", "ab", "ba", "bb", "aa", "x", "<eos>"]
    compiled = compile_grammar(vocab, 'root ::= ("a" | "b") ("a" | "b") ("a" | "b")')
    generator = torch.Generator().manual_seed(8127)
    for _ in range(24):
        selector = GreedyGrammarSelector(xgr, compiled, audit_steps=audit_steps)
        independent = xgr.GrammarMatcher(compiled)
        ids = torch.tensor([[7]])
        for _ in range(4):  # Three characters plus EOS, at most.
            scores = torch.randint(-2, 3, (1, len(vocab)), generator=generator).float()
            expected = dense_token(independent, scores)
            selected = selector(ids, scores).argmax().item()
            assert selected == expected
            assert independent.accept_token(selected)
            ids = torch.cat([ids, torch.tensor([[selected]])], dim=1)
            if independent.is_terminated():
                break
        assert independent.is_terminated() and selector.matcher.is_terminated()
        selector.validate_generated(ids[0, 1:])


@pytest.mark.skipif(not torch.cuda.is_available(), reason="CUDA unavailable")
@pytest.mark.parametrize("audit_steps", [0, 3])
def test_cuda_scores_and_inputs(compiled, audit_steps):
    selector = GreedyGrammarSelector(xgr, compiled, audit_steps=audit_steps)
    ids = torch.tensor([[4]], device="cuda")
    scores = torch.zeros((1, 6), device="cuda")
    independent = xgr.GrammarMatcher(compiled)
    for _ in range(3):
        expected = dense_token(independent, scores)
        result = selector(ids, scores)
        assert result.device == scores.device
        assert result.argmax().item() == expected
        assert independent.accept_token(expected)
        ids = torch.cat([ids, torch.tensor([[expected]], device="cuda")], dim=1)
    assert selector.matcher.is_terminated()
    selector.validate_generated(ids[0, 1:])
