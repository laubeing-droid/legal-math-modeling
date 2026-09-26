"""One grammar for spotting Lean declarations, shared by the certificate and its verifier.

Three places in this repository count `theorem` declarations: the source inventory
generator, the release certificate, and the certificate verifier. They each carried
their own regex, and they had silently drifted -- the certificate counted 1847
declarations where the inventory counted 1882 for the same files, because two of the
three ignored `@[...]`-prefixed theorems, counted keywords inside comments, or
truncated dotted names at the dot. A verifier that disagrees with its generator about
grammar produces drift errors about something nobody changed.

Comment stripping is imported from the guard scanner so there is exactly one comment
state machine in the repository.
"""

from __future__ import annotations

import re

try:
    from scripts.scan_lean_guards import strip_comments
except ImportError:  # executed as `python scripts/<name>.py`: scripts/ is sys.path[0]
    from scan_lean_guards import strip_comments

THEOREM = re.compile(r"^(?:@\[[^\]]*\][ \t]*)*theorem\s+([^\s(:{]+)")
DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*(theorem|lemma|def|structure|inductive)\s+([^\s(:{]+)"
)


def theorems(text: str) -> list[dict]:
    """Theorem declarations with 1-based line numbers; comments do not count."""

    found = []
    depth = 0
    for lineno, line in enumerate(text.splitlines(), start=1):
        code, depth = strip_comments(line, depth)
        match = THEOREM.match(code)
        if match:
            found.append({"name": match.group(1), "line": lineno})
    return found
