"""Finite conditional business semantics. No LLM, network, arbitrary checker callback,
or institutional attestation. Experimental reference, not the JC production kernel.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from datetime import date
import json
import re
from typing import Literal
from context import ContextKey, synthetic_context

World = tuple[tuple[str, bool], ...]

@dataclass(frozen=True)
class Formula:
    op: Literal['true','false','atom','not','and','or']
    atom: str = ''
    children: tuple['Formula', ...] = ()
    def __post_init__(self):
        n = len(self.children)
        if self.op not in {'true','false','atom','not','and','or'}:
            raise ValueError('UNREGISTERED_FORMULA')
        if (self.op == 'atom') != bool(self.atom):
            raise ValueError('ATOM_FIELDS')
        if (self.op in {'true','false','atom'} and n) or (self.op == 'not' and n != 1):
            raise ValueError('ARITY')
        if self.op in {'and','or'} and n != 2:
            raise ValueError('ARITY')

TRUE = Formula('true')
def Atom(s): return Formula('atom', s)
def And(a,b): return Formula('and',children=(a,b))
def Or(a,b): return Formula('or',children=(a,b))
def Not(a): return Formula('not',children=(a,))

def atom_names(f: Formula) -> set[str]:
    return ({f.atom} if f.op == 'atom' else set()).union(*(atom_names(c) for c in f.children))

def denote(f: Formula, world: World) -> bool:
    """Structural denotation; used by checker, not solver."""
    v = dict(world)
    if f.op == 'true': return True
    if f.op == 'false': return False
    if f.op == 'atom': return v[f.atom]
    if f.op == 'not': return not denote(f.children[0],world)
    if f.op == 'and': return all(denote(c,world) for c in f.children)
    return any(denote(c,world) for c in f.children)

def compile_formula(f: Formula) -> tuple[tuple[str,str], ...]:
    code = tuple(i for c in f.children for i in compile_formula(c))
    return code + ((f.op, f.atom),)

def execute(code, world: World) -> bool:
    """Stack interpreter; structurally different from denote."""
    v, stack = dict(world), []
    for op, arg in code:
        if op == 'true': stack.append(True)
        elif op == 'false': stack.append(False)
        elif op == 'atom': stack.append(v[arg])
        elif op == 'not': stack.append(not stack.pop())
        else:
            b,a=stack.pop(),stack.pop()
            stack.append(a and b if op=='and' else a or b)
    if len(stack)!=1: raise ValueError('STACK_SHAPE')
    return stack[0]

@dataclass(frozen=True)
class SourceSpan:
    source_id: str
    version: str
    body: str
    start: int
    end: int
    quoted: str
    def valid(self):
        return bool(self.source_id and self.version) and 0 <= self.start < self.end <= len(self.body) and self.body[self.start:self.end] == self.quoted

@dataclass(frozen=True)
class Payment:
    payment_id: str
    amount: Q
    event_day: date
    payer: str
    recipient: str
    debt_id: str
    recognition_atom: str
    source_id: str

@dataclass(frozen=True)
class PrincipalSpec:
    context: ContextKey
    relation_id: str
    creditor: str
    debtor: str
    debt_id: str
    principal: Q
    due_day: date
    asof_day: date
    sources: tuple[SourceSpan, ...]
    payments: tuple[Payment, ...]
    facts: tuple[tuple[str, bool | None], ...]
    constraint: Formula = TRUE
    approved_policy: str = 'SYNTHETIC-CONDITIONAL-PRINCIPAL/1'
    # This fragment computes a matured, admitted principal balance only.
    # Other claims, defenses, taxes, interest and judgments are NOT modelled.
    def validate(self):
        if type(self.context) is not ContextKey or any(type(x) is not tuple for x in (self.sources,self.payments,self.facts)):
            raise ValueError('IMMUTABLE_TYPED_SPEC_REQUIRED')
        if self.approved_policy != 'SYNTHETIC-CONDITIONAL-PRINCIPAL/1':
            raise ValueError('UNSUPPORTED_POLICY')
        if any(not isinstance(x,str) or not x or any(ord(c)<32 or c in '\u202a\u202b\u202c\u202d\u202e\u2066\u2067\u2068\u2069' for c in x)
               for x in (self.relation_id,self.creditor,self.debtor,self.debt_id)):
            raise ValueError('IDENTITY')
        if self.creditor==self.debtor: raise ValueError('FRAGMENT_REQUIRES_DISTINCT_PARTIES')
        if type(self.principal) is not Q or self.principal<0: raise ValueError('MONEY_TYPE')
        if self.asof_day < self.due_day: raise ValueError('NOT_DUE_IN_THIS_FRAGMENT')
        if self.context.event_time != self.due_day.isoformat() or self.context.decision_time != self.asof_day.isoformat():
            raise ValueError('TEMPORAL_BINDING')
        if self.context.scenario != 'finite-conditional-completions' or not self.context.assumptions:
            raise ValueError('CONDITIONAL_SCOPE_REQUIRED')
        ids=[s.source_id for s in self.sources]
        if not ids or len(ids)!=len(set(ids)) or not all(s.valid() for s in self.sources):
            raise ValueError('SOURCE_BINDING')
        keys=[k for k,_ in self.facts]
        if len(keys)!=len(set(keys)) or any(not k or v is not None and type(v) is not bool for k,v in self.facts):
            raise ValueError('FACT_SCHEMA')
        if not atom_names(self.constraint)<=set(keys): raise ValueError('UNDECLARED_CONSTRAINT_ATOM')
        pids=[p.payment_id for p in self.payments]
        if len(pids)!=len(set(pids)): raise ValueError('DUPLICATE_PAYMENT')
        for p in self.payments:
            if type(p.amount) is not Q or p.amount<0: raise ValueError('PAYMENT_AMOUNT')
            if p.event_day>self.asof_day: raise ValueError('FUTURE_PAYMENT')
            if (p.payer,p.recipient,p.debt_id)!=(self.debtor,self.creditor,self.debt_id):
                raise ValueError('PAYMENT_PARTY_OR_DEBT')
            if p.recognition_atom not in keys or p.source_id not in ids: raise ValueError('PAYMENT_BASIS')

def solver_worlds(spec: PrincipalSpec) -> tuple[World, ...]:
    spec.validate()
    keys=[k for k,_ in spec.facts]
    options=[(False,True) if v is None else (v,) for _,v in spec.facts]
    code=compile_formula(spec.constraint)
    return tuple(w for vs in product(*options) if execute(code,w:=tuple(zip(keys,vs))))

def valid_world(spec: PrincipalSpec, w: World) -> bool:
    return type(w) is tuple and len(w)==len(spec.facts) and all(
        type(pair) is tuple and len(pair)==2 and pair[0]==k and type(pair[1]) is bool
        for pair,(k,_) in zip(w,spec.facts))

def checker_worlds(spec: PrincipalSpec) -> frozenset[World]:
    """Enumerate every Boolean assignment independently, then restrict it."""
    spec.validate()
    keys=[k for k,_ in spec.facts]; facts=dict(spec.facts)
    candidates=[]
    for mask in range(1 << len(keys)):
        w=tuple((k,bool(mask & (1<<i))) for i,k in enumerate(keys))
        if all(facts[k] is None or facts[k] is val for k,val in w) and denote(spec.constraint,w):
            candidates.append(w)
    return frozenset(candidates)

@dataclass(frozen=True)
class Outcome:
    context: ContextKey
    relation_id: str
    creditor: str
    debtor: str
    debt_id: str
    basis_ids: tuple[str, ...]
    asof_day: date
    world: World
    principal_balance: Q
    overpayment_residual: Q
    conclusion_kind: str = 'CONDITIONAL_PRINCIPAL_BALANCE_NOT_JUDGMENT'

@dataclass(frozen=True)
class Result:
    context: ContextKey
    mode: Literal['EXACT_FINITE_SCENARIOS','PARTIAL_SCENARIOS','INCONSISTENT_ASSUMPTIONS']
    outcomes: tuple[Outcome, ...]
    pending: tuple[World, ...]

def solve(spec: PrincipalSpec, budget: int | None=None) -> Result:
    if budget is not None and (type(budget) is not int or budget<0): raise ValueError('BUDGET')
    worlds=solver_worlds(spec)
    if not worlds: return Result(spec.context,'INCONSISTENT_ASSUMPTIONS',(),())
    n=len(worlds) if budget is None else min(budget,len(worlds))
    results=[]
    for w in worlds[:n]:
        paid=sum((p.amount for p in spec.payments if dict(w)[p.recognition_atom]),Q(0))
        residual=spec.principal-paid
        results.append(Outcome(spec.context,spec.relation_id,spec.creditor,spec.debtor,spec.debt_id,
                      tuple(s.source_id for s in spec.sources),spec.asof_day,w,max(residual,Q(0)),max(-residual,Q(0))))
    return Result(spec.context,'EXACT_FINITE_SCENARIOS' if n==len(worlds) else 'PARTIAL_SCENARIOS',tuple(results),worlds[n:])

def check(spec: PrincipalSpec, report: Result) -> bool:
    """Fixed checker. No callback, no execution of certificate-supplied code.
    Uses conservation + nonnegative complementary residuals rather than max()."""
    try:
        if type(report) is not Result or report.context!=spec.context: return False
        domain=checker_worlds(spec)
        if not domain:
            return report.mode=='INCONSISTENT_ASSUMPTIONS' and not report.outcomes and not report.pending
        if report.mode not in {'EXACT_FINITE_SCENARIOS','PARTIAL_SCENARIOS'}: return False
        seen=[]
        for o in report.outcomes:
            if type(o) is not Outcome: return False
            if (o.context,o.relation_id,o.creditor,o.debtor,o.debt_id,o.basis_ids,o.asof_day,o.conclusion_kind)!=(
                spec.context,spec.relation_id,spec.creditor,spec.debtor,spec.debt_id,
                tuple(s.source_id for s in spec.sources),spec.asof_day,'CONDITIONAL_PRINCIPAL_BALANCE_NOT_JUDGMENT'):
                return False
            if not valid_world(spec,o.world) or o.world not in domain or o.world in seen: return False
            seen.append(o.world)
            c,u=o.principal_balance,o.overpayment_residual
            if type(c) is not Q or type(u) is not Q or min(c,u)<0 or c*u!=0: return False
            total=Q(0)
            for p in spec.payments:
                if dict(o.world)[p.recognition_atom]: total+=p.amount
            if c-u+total != spec.principal: return False
        if any(not valid_world(spec,w) for w in report.pending): return False
        if len(set(report.pending))!=len(report.pending): return False
        if set(seen)&set(report.pending) or frozenset(seen)|frozenset(report.pending)!=domain: return False
        if report.mode=='EXACT_FINITE_SCENARIOS': return not report.pending
        return bool(report.pending)
    except (ValueError,TypeError,KeyError,AttributeError):
        return False

@dataclass(frozen=True)
class DecisionInputs:
    context: ContextKey
    weights: tuple[tuple[World,Q], ...]
    threshold: Q
    costs: tuple[Q,Q,Q,Q]
    legal_options: tuple[Q, ...]
    basis: str = 'SYNTHETIC-SETTLEMENT-GRID/1'

@dataclass(frozen=True)
class Analytics:
    context: ContextKey
    weights: tuple[tuple[World,Q], ...]
    threshold: Q
    expected: Q
    event_probability: Q
    plaintiff_cost: Q
    defendant_cost: Q
    plaintiff_settle_cost: Q
    defendant_settle_cost: Q
    lower: Q
    upper: Q
    legal_options: tuple[Q, ...]
    mutually_acceptable: tuple[Q, ...]
    selected: Q | None

def validate_decision_inputs(spec,result,m):
    if type(m) is not DecisionInputs or m.context!=spec.context or m.basis!='SYNTHETIC-SETTLEMENT-GRID/1':
        raise ValueError('MODEL_BINDING')
    if not check(spec,result) or result.mode!='EXACT_FINITE_SCENARIOS': raise ValueError('COMPLETE_SCENARIOS_REQUIRED')
    amounts={o.world:o.principal_balance for o in result.outcomes}
    if type(m.weights) is not tuple or len(m.weights)!=len(dict(m.weights)) or set(dict(m.weights))!=set(amounts):
        raise ValueError('MODEL_WORLD_COVERAGE')
    if any(not valid_world(spec,w) or type(p) is not Q or p<0 for w,p in m.weights) or sum((p for _,p in m.weights),Q(0))!=1:
        raise ValueError('PROBABILITY_SPACE')
    if type(m.threshold) is not Q or type(m.costs) is not tuple or len(m.costs)!=4 or any(type(c) is not Q or c<0 for c in m.costs):
        raise ValueError('MODEL_QUANTITIES')
    if type(m.legal_options) is not tuple or len(set(m.legal_options))!=len(m.legal_options) or any(type(c) is not Q or c<0 for c in m.legal_options):
        raise ValueError('DECLARED_ACTION_SET')

def derive_analytics(spec,result,m:DecisionInputs) -> Analytics:
    validate_decision_inputs(spec,result,m)
    amounts={o.world:o.principal_balance for o in result.outcomes}
    cp,cd,sp,sd=m.costs
    expected=sum((p*amounts[w] for w,p in m.weights),Q(0))
    prob=sum((p for w,p in m.weights if amounts[w]>=m.threshold),Q(0))
    lo,hi=expected-cp+sp,expected+cd-sd
    legal=tuple(sorted(m.legal_options))
    eligible=tuple(s for s in legal if lo<=s<=hi)
    return Analytics(spec.context,m.weights,m.threshold,expected,prob,cp,cd,sp,sd,lo,hi,legal,eligible,eligible[0] if eligible else None)

def check_analytics(spec,result,m:DecisionInputs,a:Analytics)->bool:
    try:
        validate_decision_inputs(spec,result,m)
        if type(a) is not Analytics or a.context!=spec.context:return False
        if any(type(x) is not Q for x in (a.threshold,a.expected,a.event_probability,a.plaintiff_cost,a.defendant_cost,a.plaintiff_settle_cost,a.defendant_settle_cost,a.lower,a.upper)):return False
        if a.selected is not None and type(a.selected) is not Q:return False
        if any(type(x) is not Q for x in a.legal_options+a.mutually_acceptable):return False
        if (a.weights,a.threshold,(a.plaintiff_cost,a.defendant_cost,a.plaintiff_settle_cost,a.defendant_settle_cost),set(a.legal_options))!=(m.weights,m.threshold,m.costs,set(m.legal_options)):return False
        if len(a.legal_options)!=len(m.legal_options):return False
        table={o.world:o.principal_balance for o in result.outcomes}
        expectation=Q(0); event=Q(0)
        for w,p in m.weights:
            expectation+=table[w]*p
            if table[w]>=m.threshold:event+=p
        if (a.expected,a.event_probability)!=(expectation,event):return False
        if a.lower+m.costs[0]-m.costs[2]!=expectation:return False
        if a.upper-m.costs[1]+m.costs[3]!=expectation:return False
        eligible={s for s in m.legal_options if a.lower<=s<=a.upper}
        if set(a.mutually_acceptable)!=eligible or len(a.mutually_acceptable)!=len(eligible):return False
        return (a.selected is None and not eligible) or a.selected in eligible
    except (ValueError,TypeError,KeyError,AttributeError):return False

WARNING='本文件为明确假设下的条件计算，不表示法院认定、真实胜率或最终返还请求已经成立。'
FOOTER='范围仅限本输入指定的本金余额；利息、其他抗辩、法律审核和实际裁判另行处理。'
def _j(x):return json.dumps(x,ensure_ascii=False,separators=(',',':'),sort_keys=True)
def _q(x):return str(x.numerator) if x.denominator==1 else f'{x.numerator}/{x.denominator}'

def render(spec:PrincipalSpec,result:Result)->str:
    if not check(spec,result):raise ValueError('UNCHECKED_RESULT')
    lines=['# 条件性本金分析',WARNING,'案件：'+_j(spec.context.request),'争点：'+_j(spec.context.issue),
           '权利人：'+_j(spec.creditor),'义务人：'+_j(spec.debtor),'债项：'+_j(spec.debt_id),
           '依据：'+_j(list(s.source_id for s in spec.sources)),
           '到期日：'+spec.due_day.isoformat(),'观察日：'+spec.asof_day.isoformat(),
           '假设：'+_j(list(spec.context.assumptions)),
           '共同语境：'+spec.context.canonical_json(),
           '结论状态：'+result.mode]
    for o in result.outcomes:
        lines.append('情景：'+_j(dict(o.world))+'；本金余额：'+_q(o.principal_balance)+' 元；超付残差：'+_q(o.overpayment_residual)+' 元；性质：条件计算')
    for w in result.pending:lines.append('待求情景：'+_j(dict(w)))
    lines.append(FOOTER)
    return '\n'.join(lines)+'\n'

def _load_unique(text):
    def pairs(ps):
        d={}
        for k,v in ps:
            if k in d:raise ValueError('DUPLICATE_JSON_KEY')
            d[k]=v
        return d
    return json.loads(text,object_pairs_hook=pairs)

def verify_document(spec:PrincipalSpec,result:Result,text:str)->bool:
    """Read the actual UTF-8 text; no reliance on an invisible sidecar.
    A closed grammar rejects extra paragraphs rather than claiming free-text entailment.
    Does not call render(). NOT a generic DOCX/PDF/Markdown semantic verifier."""
    if not check(spec,result):return False
    try:
        lines=text.splitlines()
        if len(lines)<14 or lines[0]!='# 条件性本金分析' or lines[1]!=WARNING or lines[-1]!=FOOTER:return False
        labels=('案件','争点','权利人','义务人','债项','依据','到期日','观察日','假设','共同语境','结论状态')
        obj={}
        for ln,k in zip(lines[2:13],labels):
            prefix=k+'：'
            if not ln.startswith(prefix):return False
            obj[k]=ln[len(prefix):]
        if tuple(_load_unique(obj[k]) for k in labels[:5])!=(spec.context.request,spec.context.issue,spec.creditor,spec.debtor,spec.debt_id):return False
        if _load_unique(obj['依据'])!=[s.source_id for s in spec.sources]:return False
        if obj['到期日']!=spec.due_day.isoformat() or obj['观察日']!=spec.asof_day.isoformat():return False
        if _load_unique(obj['假设'])!=list(spec.context.assumptions):return False
        if ContextKey.from_json(obj['共同语境'])!=spec.context or obj['结论状态']!=result.mode:return False
        got=[];pending=[]
        for ln in lines[13:-1]:
            if ln.startswith('待求情景：'):
                w=_load_unique(ln[len('待求情景：'):])
                if type(w) is not dict or any(type(v) is not bool for v in w.values()):return False
                pending.append(tuple(sorted(w.items())));continue
            m=re.fullmatch(r'情景：(.+)；本金余额：(-?\d+(?:/\d+)?) 元；超付残差：(-?\d+(?:/\d+)?) 元；性质：条件计算',ln)
            if not m:return False
            w=_load_unique(m[1])
            if type(w) is not dict or any(type(v) is not bool for v in w.values()):return False
            got.append((tuple(sorted(w.items())),Q(m[2]),Q(m[3])))
        expected=[(tuple(sorted(o.world)),o.principal_balance,o.overpayment_residual) for o in result.outcomes]
        return sorted(got)==sorted(expected) and sorted(pending)==sorted(tuple(sorted(w)) for w in result.pending)
    except (ValueError,TypeError,KeyError,ZeroDivisionError,json.JSONDecodeError):return False


def demo_spec(**changes):
    ctx=synthetic_context(request='DEMO-PRINCIPAL-01',issue='principal-balance',event_time='2026-08-01',decision_time='2026-09-09',
        scenario='finite-conditional-completions',assumptions=('债权成立与到期已作为示例前提','仅付款认定作为分支','非真实法律案件'))
    source='合成示例：已到期本金1000元；争议清偿300元；只计算条件本金余额。'
    base=dict(context=ctx,relation_id='principal-claim',creditor='甲公司',debtor='乙公司',debt_id='DEBT-1',principal=Q(1000),
              due_day=date(2026,8,1),asof_day=date(2026,9,9),sources=(SourceSpan('SYNTHETIC-BASIS','1',source,0,len(source),source),),
              payments=(Payment('P1',Q(300),date(2026,8,20),'乙公司','甲公司','DEBT-1','payment_recognized','SYNTHETIC-BASIS'),),
              facts=(('payment_recognized',None),))
    base.update(changes)
    return PrincipalSpec(**base)
