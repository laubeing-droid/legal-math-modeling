"""Dependency-sensitive exclusion/revision; no silent reuse of derived material."""
def affected_closure(changed,dependencies):
    affected=set(changed)
    while True:
        nxt=affected|{obj for obj,deps in dependencies.items() if set(deps)&affected}
        if nxt==affected:return frozenset(nxt)
        affected=nxt

def reusable(prior_binding,new_binding,artifact,changed,dependencies):
    return prior_binding==new_binding and artifact not in affected_closure(changed,dependencies)
