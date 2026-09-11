"""Occurrence-preserving tree graph and guarded legacy atom-graph projection."""
from dataclasses import dataclass
from unified.arguments import Argument

@dataclass(frozen=True)
class OccurrenceGraph:
    nodes: tuple[tuple[tuple[int,...],str,str|None,str|None,frozenset],...]
    edges: frozenset[tuple[tuple[int,...],tuple[int,...]]]


def to_occurrence_graph(root: Argument):
    nodes=[];edges=set()
    def visit(node,path):
        nodes.append((path,node.head,node.rule,node.leaf,node.assumptions))
        for i,child in enumerate(node.children):
            cp=path+(i,);edges.add((cp,path));visit(child,cp)
    visit(root,())
    return OccurrenceGraph(tuple(nodes),frozenset(edges))


def occurrence_graph_well_founded(graph):
    paths={p for p,*_ in graph.nodes}
    return (len(paths)==len(graph.nodes) and () in paths
            and all(child in paths and parent in paths and len(child)==len(parent)+1
                    and child[:-1]==parent for child,parent in graph.edges))


def legacy_projection(root):
    """Refuse atom-collapsing cycles. Full ULM08 refinement remains a proof task."""
    graph=to_occurrence_graph(root)
    if not occurrence_graph_well_founded(graph): raise ValueError('Invalid support occurrences')
    labels={p:head for p,head,*_ in graph.nodes}
    edges={(labels[c],labels[p]) for c,p in graph.edges}
    adjacency={head:set() for head in labels.values()}
    for a,b in edges:adjacency[a].add(b)
    visiting=set();done=set()
    def cycle(a):
        if a in visiting:return True
        if a in done:return False
        visiting.add(a)
        if any(cycle(b) for b in adjacency[a]):return True
        visiting.remove(a);done.add(a);return False
    if any(cycle(a) for a in adjacency):
        raise ValueError('ATOM_COLLAPSE_CYCLE: no established ULM08 correspondence')
    return {'occurrences':graph,'atom_edges':frozenset(edges),
            'assurance':'acyclic_projection_only_not_full_refinement'}


def require_declared_scope(context, *, requested_unbounded=False):
    if requested_unbounded and context.semantic_scope!='unbounded-with-coverage-proof':
        raise ValueError('Depth-scoped extensions cannot claim unbounded soundness')
    return {'semantic_scope':context.semantic_scope,'height':context.max_depth}
