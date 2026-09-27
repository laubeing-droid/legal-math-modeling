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

# Names that enter the environment and therefore collide across imports. `instance`
# and `example` are excluded: they are anonymous, so Lean tolerates repeats.
ENV_DECLARATION = re.compile(
    r"^(?:@\[[^\]]*\][ \t]*)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|opaque|notation3|notation|macro)"
    r"\s+([^\s(:{=\[]+)"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)")
END_BLOCK = re.compile(r"^end\s+([A-Za-z0-9_.]+)?\s*$")


def declarations(text: str, *, namespace: bool = False) -> list[dict]:
    """Environment-level declarations with 1-based lines.

    `namespace=True` qualifies each name by the enclosing `namespace` blocks, which
    is what the environment actually holds: two files may each define `isSelfAttack`
    under different namespaces, and only the qualified name decides whether an
    `import` conflicts. `private` declarations are skipped because they are invisible
    outside their own module and so cannot collide.
    """

    found = []
    depth = 0
    stack: list[str] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        code, depth = strip_comments(line, depth)
        stripped = code.strip()
        opened = NAMESPACE.match(stripped)
        if opened:
            stack.append(opened.group(1))
            continue
        closed = END_BLOCK.match(stripped)
        if closed and stack:
            target = closed.group(1)
            if target is None or stack[-1].endswith(target):
                stack.pop()
            continue
        match = ENV_DECLARATION.match(stripped)
        if match and "private" not in stripped.split(match.group(2))[0]:
            name = match.group(2)
            if namespace and stack:
                name = ".".join(stack) + "." + name
            found.append({"keyword": match.group(1), "name": name, "line": lineno})
    return found


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
