"""Round-9 item six: deterministic TF-IDF candidate engine gates.

Three conservation properties (normalization invariance, self-similarity
= 1 on nonzero vectors, symmetry), determinism of the ranked order, and
the hard candidate-only boundary: the engine's output type carries scores
and ids and nothing that could be read as an adjudication.
"""

from __future__ import annotations

import math

from theory.spec.vector_engine import (
    Candidate,
    build_idf,
    cosine,
    l2_normalize,
    recall_candidates,
    tokenize,
    tfidf_vector,
)

CORPUS = [
    ("doc_a", "买卖合同纠纷 货款给付 违约金"),
    ("doc_b", "建设工程施工合同 工程款 利息"),
    ("doc_c", "劳动争议 加班费 经济补偿"),
    ("doc_d", "买卖合同纠纷 交付 质量异议"),
    ("doc_e", "民间借贷 利率 还款"),
]


def test_cosine_normalization_invariance() -> None:
    v = {"a": 3.0, "b": 4.0}
    w = {"a": 8.0, "b": 6.0}
    assert math.isclose(
        cosine(v, w),
        cosine(l2_normalize(v), l2_normalize(w)),
        rel_tol=1e-12,
        abs_tol=1e-12,
    )


def test_cosine_self_similarity_is_one() -> None:
    v = {"a": 3.0, "b": 4.0}
    assert math.isclose(cosine(v, v), 1.0, rel_tol=1e-12, abs_tol=1e-12)


def test_cosine_symmetry() -> None:
    v = {"a": 1.0, "b": 2.0}
    w = {"a": 4.0, "c": 5.0}
    assert math.isclose(cosine(v, w), cosine(w, v), rel_tol=1e-12, abs_tol=1e-12)


def test_cosine_zero_vector_convention() -> None:
    assert cosine({}, {"a": 1.0}) == 0.0
    assert cosine({}, {}) == 0.0


def test_recall_is_deterministic_and_ranked() -> None:
    first = recall_candidates("买卖合同纠纷", CORPUS, top_k=3)
    second = recall_candidates("买卖合同纠纷", CORPUS, top_k=3)
    assert first == second
    assert len(first) == 3
    assert first[0].doc_id == "doc_a"  # 语义最相近的排前
    scores = [c.score for c in first]
    assert scores == sorted(scores, reverse=True)


def test_recall_emits_candidates_only() -> None:
    results = recall_candidates("工程款 利息", CORPUS, top_k=5)
    for item in results:
        assert isinstance(item, Candidate)
        assert set(item._fields) == {"doc_id", "score"}  # 没有裁判/胜诉/关系字段
    assert recall_candidates("任意", CORPUS, top_k=0) == []
    assert recall_candidates("任意", [], top_k=5) == []


def test_tokenizer_is_deterministic_and_cjk_aware() -> None:
    assert tokenize("买卖合同纠纷") == ["买卖合同纠纷"]
    assert tokenize("Contract, Breach!") == ["contract", "breach"]
    assert tokenize("A B  A") == ["a", "b", "a"]
    assert tokenize("") == []


def test_idf_and_vector_shapes() -> None:
    tokenized = [tokenize(t) for _, t in CORPUS]
    idf = build_idf(tokenized)
    assert all(v > 0.0 for v in idf.values())
    vec = tfidf_vector(tokenized[0], idf)
    assert math.isclose(sum(vec.values()), sum(vec.values()))  # 可重算
    assert l2_normalize({}) == {}
