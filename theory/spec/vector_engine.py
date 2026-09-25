#!/usr/bin/env python3
"""Deterministic TF-IDF vector candidate engine (round-9 item six).

Recall layer one made real: a pure-Python, zero-dependency TF-IDF cosine
engine over synthetic corpora. Hard boundary — it emits Top-K candidate
documents with scores and nothing else: no win rate, no adjudication, no
relation characterization, no "most similar therefore decide thus".
Output is capped at candidate grade by construction; structural
comparison remains the exclusive province of layer two.
"""

from __future__ import annotations

import math
from typing import Dict, List, Sequence, Tuple

Token = str
Vector = Dict[Token, float]


def tokenize(text: str) -> List[Token]:
    """Deterministic tokenizer: same string in, same token sequence out.

    No model, no external service — lowercase, then split on any run of
    non-alphanumeric-or-CJK characters.
    """

    tokens: List[Token] = []
    current: List[str] = []

    def is_word_char(ch: str) -> bool:
        return ch.isalnum() or "\u4e00" <= ch <= "\u9fff"

    for ch in text.lower():
        if is_word_char(ch):
            current.append(ch)
        elif current:
            tokens.append("".join(current))
            current = []
    if current:
        tokens.append("".join(current))
    return tokens


def document_frequency(tokenized_docs: Sequence[Sequence[Token]]) -> Dict[Token, int]:
    df: Dict[Token, int] = {}
    for doc in tokenized_docs:
        for token in set(doc):
            df[token] = df.get(token, 0) + 1
    return df


def build_idf(tokenized_docs: Sequence[Sequence[Token]]) -> Dict[Token, float]:
    n = len(tokenized_docs)
    if n == 0:
        return {}
    df = document_frequency(tokenized_docs)
    return {t: math.log((n + 1) / (d + 1)) + 1.0 for t, d in df.items()}


def tfidf_vector(doc: Sequence[Token], idf: Dict[Token, float]) -> Vector:
    counts: Dict[Token, int] = {}
    for token in doc:
        counts[token] = counts.get(token, 0) + 1
    total = len(doc)
    if total == 0:
        return {}
    return {
        t: (c / total) * idf.get(t, 1.0) for t, c in counts.items()
    }


def dot(v: Vector, w: Vector) -> float:
    return sum(a * w.get(t, 0.0) for t, a in v.items())


def l2_norm(v: Vector) -> float:
    return math.sqrt(sum(a * a for a in v.values()))


def l2_normalize(v: Vector) -> Vector:
    n = l2_norm(v)
    if n == 0.0:
        return {}
    return {t: a / n for t, a in v.items()}


def cosine(v: Vector, w: Vector) -> float:
    """Cosine similarity; zero vectors conventionally score 0."""

    nv = l2_norm(v)
    nw = l2_norm(w)
    if nv == 0.0 or nw == 0.0:
        return 0.0
    return dot(v, w) / (nv * nw)


from typing import NamedTuple


class Candidate(NamedTuple):
    doc_id: str
    score: float


def recall_candidates(
    query: str,
    corpus: Sequence[Tuple[str, str]],
    top_k: int = 10,
) -> List[Candidate]:
    """Top-K candidate recall: score-descending, doc_id-ascending tie-break.

    The result ordering is fixed by contract for identical inputs; every
    emitted item is a candidate and nothing more.
    """

    if top_k <= 0 or not corpus:
        return []
    tokenized = [(doc_id, tokenize(text)) for doc_id, text in corpus]
    idf = build_idf([tokens for _, tokens in tokenized])
    query_vec = tfidf_vector(tokenize(query), idf)
    scored = [
        Candidate(doc_id, cosine(query_vec, tfidf_vector(tokens, idf)))
        for doc_id, tokens in tokenized
    ]
    ranked = sorted(scored, key=lambda item: (-item.score, item.doc_id))
    return ranked[:top_k]
