"""T122/T123 interpretation layer tests (K rows 2551-2552).

T122: five interpretation constructors with named reasons and the adoption
gate — construction is NOT adoption; non-adopted candidates never enter the
rule base (the row's original counterexample, kept independently).
T123: branch compatibility/attack/priority and the branch-isolation gate —
a derivation citing another branch's premises is REJECTED (the row's
original counterexample, kept independently).
Plus the independent-checker differential and the completion/validate
receipt for the six-piece closure.
"""
import ast
import importlib.util
from pathlib import Path

import pytest

from tools.full_math.implementation import interpretation_ref as R
from tools.full_math.implementation import interp_ref_check as K

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]


def _load_completion():
    """Load tools/full_math/completion.py by explicit path — NO sys.path
    insert: tools/full_math carries a `reference` package that would shadow
    tools/unified_math_v2/reference in a shared pytest process."""
    path = REPO / 'tools/full_math/completion.py'
    spec = importlib.util.spec_from_file_location('completion_t122_t123',
                                                  str(path))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


C = _load_completion()

LEAN_MODULE = (REPO / 'proofs/lean/juris_lean/JurisLean/Seams/'
               'UnifiedW4Interp.lean')

RULE_A = R.RuleAst(rule_id="R-1", premises=("contract_signed",),
                   conclusion="payment_due")
RULE_B = R.RuleAst(rule_id="R-2", premises=("usage_evidenced",),
                   conclusion="payment_due")
INPUT_X = R.InterpInput(text_id="art7-text", context_ids=("mat-11",))
INPUT_Y = R.InterpInput(text_id="art7-text", context_ids=("mat-22",))

ALL_METHODS = [
    R.InterpMethod.LITERAL, R.InterpMethod.SYSTEMATIC,
    R.InterpMethod.TELEOLOGICAL, R.InterpMethod.HISTORICAL,
    R.InterpMethod.CONSTITUTIONAL,
]

MK_BY_METHOD = {
    R.InterpMethod.LITERAL: R.mk_literal,
    R.InterpMethod.SYSTEMATIC: R.mk_systematic,
    R.InterpMethod.TELEOLOGICAL: R.mk_teleological,
    R.InterpMethod.HISTORICAL: R.mk_historical,
}


def _cand(cid="c1", method=R.InterpMethod.LITERAL, inp=INPUT_X,
          target="art7", rule=RULE_A, reason="reason-1",
          authority="court-9"):
    return R.mk_candidate(method, cid, inp, "art7", "civil",
                          R.InterpEffect.SELECT_READING, rule, reason,
                          authority)


# ---------------------------------------------------------------------------
# T122: 五解释构造（构造子＋理由字段＋合法性）
# ---------------------------------------------------------------------------


def test_method_set_is_exactly_five_and_analogy_is_outside():
    """§11.2 修正注记：五法为文义/体系/目的/历史/合宪；类推另列漏洞续造构造子，
    不在解释方法集内（对照 Lean five_methods_exhaust/pairwise_ne）。"""
    assert set(ALL_METHODS) == set(R.InterpMethod)
    assert len(R.InterpMethod) == 5
    assert K.check_method_set().ok


@pytest.mark.parametrize('method', ALL_METHODS,
                         ids=[m.value for m in ALL_METHODS])
def test_constructor_preserves_input_face(method):
    """P066：构造子保存输入文本/目标/范围/效应，理由具名
    （对照 Lean *_legal 六面合取）。"""
    cid = 'c-' + method.value
    if method is R.InterpMethod.CONSTITUTIONAL:
        c = R.mk_constitutional(cid, INPUT_X, 'art7', 'civil',
                                R.InterpEffect.SELECT_READING, RULE_A,
                                'reason-1', 'court-9')
    else:
        c = MK_BY_METHOD[method](cid, INPUT_X, 'art7', 'civil',
                                 R.InterpEffect.SELECT_READING, RULE_A,
                                 'reason-1')
    assert c.input is INPUT_X and c.input.text_id == 'art7-text'
    assert c.target == 'art7' and c.scope == 'civil'
    assert c.effect is R.InterpEffect.SELECT_READING
    assert c.reason_id == 'reason-1' and c.method is method


def test_unnamed_reason_rejected():
    """§3.1：构造子输出必须带具名理由（fail-fast，不收空理由）。"""
    with pytest.raises(ValueError):
        R.mk_candidate(R.InterpMethod.LITERAL, 'c1', INPUT_X, 'art7',
                       'civil', R.InterpEffect.SELECT_READING, RULE_A, None)


def test_constitutional_requires_authority():
    """P066：合宪解释受相应制度权限约束——无权限的合宪候选直接拒绝。"""
    with pytest.raises(ValueError):
        R.mk_constitutional('c9', INPUT_X, 'art7', 'civil',
                            R.InterpEffect.SELECT_READING, RULE_A,
                            'reason-9', None)
    ok = R.mk_constitutional('c9', INPUT_X, 'art7', 'civil',
                             R.InterpEffect.SELECT_READING, RULE_A,
                             'reason-9', 'court-9')
    assert R.adoptable(ok)


def test_construction_is_not_adoption():
    """§3.1：使用方法≠采用——构造子不内置权限，缺权限候选不可采用。"""
    c = R.mk_literal('c1', INPUT_X, 'art7', 'civil',
                     R.InterpEffect.SELECT_READING, RULE_A, 'reason-1')
    assert c.authority_id is None and not R.adoptable(c)


def test_method_use_not_proof_of_correctness():
    """T122 原反例（独立保留）：只跑了文义方法、无采用权限的候选被采用门拒绝，
    其规则不进规则库——'使用了某方法'不自动证明解释正确
    （对照 Lean method_use_not_proof_of_correctness/unauth_rule_not_in_base）。"""
    unauth = R.mk_literal('c99', INPUT_X, 'art7', 'civil',
                          R.InterpEffect.SELECT_READING, RULE_A, 'reason-1')
    assert not R.adoptable(unauth)
    assert unauth.rule not in R.rule_base([unauth])


def test_rule_base_only_adopted():
    """§3.1：未采用候选不进入无条件规则库；库中每条规则都有可合法采用载体。"""
    auth = _cand('c1')
    unauth = R.mk_literal('c2', INPUT_Y, 'art7', 'civil',
                          R.InterpEffect.SELECT_READING, RULE_B, 'reason-2')
    assert R.rule_base([auth, unauth]) == frozenset({RULE_A})


def test_rule_base_omits_unadoptable_injective():
    """规则库排除（一般形）：候选唯一携带其规则且不可合法采用时规则不进库。"""
    x = R.mk_candidate(R.InterpMethod.SYSTEMATIC, 'cx', INPUT_Y, 'art7',
                       'civil', R.InterpEffect.SELECT_READING, RULE_B,
                       'reason-x', None)
    others = [_cand('o1'), _cand('o2', rule=R.RuleAst('R-3', ('p',), 'q'))]
    assert not R.adoptable(x)
    uniq = all(c.rule != x.rule for c in others)
    assert uniq and x.rule not in R.rule_base(others + [x])


def test_adoption_adds_only_rule():
    """P066：采用只增规则 AST 本身，不附带宣告法源失效等额外权力。"""
    c = _cand('c1')
    others = [_cand('o1', rule=RULE_B)]
    base = R.rule_base([c] + others)
    assert base == frozenset({RULE_A, RULE_B})


# ---------------------------------------------------------------------------
# T123: 解释分支（相容/攻击/优先 ＋ 分支隔离）
# ---------------------------------------------------------------------------


def _two_candidates_and_branches():
    x = _cand('c1', method=R.InterpMethod.LITERAL, inp=INPUT_X, rule=RULE_A)
    y = _cand('c2', method=R.InterpMethod.SYSTEMATIC, inp=INPUT_Y,
              rule=RULE_B)
    bx, by = R.branch_each([x, y])
    return x, y, bx, by


def test_conflict_attack_and_compatibility():
    """§3.1 相互攻击 ＋ §4.3 靶点冲突：攻击对称，无冲突则相容
    （对照 Lean interpAttack_symmetric/witness_attack_both_ways）。"""
    x, y, bx, by = _two_candidates_and_branches()
    assert R.conflict_on(x, y)
    assert R.interp_attack(bx, by, [x, y])
    assert R.interp_attack(by, bx, [x, y])  # 相互攻击
    far = _cand('c3', method=R.InterpMethod.HISTORICAL, rule=RULE_A,
                target='art9')
    assert not R.conflict_on(x, far)


def test_priority_requires_conflict():
    """§3.1：无冲突不造优先边（PriorityWF 只落在真冲突上）。"""
    x, y, _bx, _by = _two_candidates_and_branches()
    far = _cand('c3', rule=RULE_A, target='art9')
    assert R.priority_wf((R.PriorityPair('c1', 'c2'),), (x, y))
    assert not R.priority_wf((R.PriorityPair('c1', 'c3'),), (x, far))


def test_priority_resolves_superior():
    """§3.1 profile：具名边 1→2 时采用集收敛到优位支
    （对照 Lean witness_superior_adopted）。"""
    x, y, _bx, _by = _two_candidates_and_branches()
    resolved = R.resolved_by_priority((R.PriorityPair('c1', 'c2'),), (x, y))
    assert [c.candidate_id for c in resolved] == ['c1']
    # 反向边同样收敛到它声明的优位（c2→c1 时留下 c2）
    rev = R.resolved_by_priority((R.PriorityPair('c2', 'c1'),), (x, y))
    assert [c.candidate_id for c in rev] == ['c2']


def test_no_priority_keeps_both_and_refers():
    """§3.1：同位无法定胜负——全保留并记报请路径，不作选择
    （对照 Lean witness_no_priority_keeps_both/witness_two_branches_kept）。"""
    x, y, bx, by = _two_candidates_and_branches()
    assert [c.candidate_id for c in R.resolved_by_priority((), (x, y))] == \
        ['c1', 'c2']
    assert bx.branch_id != by.branch_id  # 支路保留不合并
    layer = R.build_interp_layer([x, y])
    assert ('c1', 'c2') in layer.referral
    assert len(layer.branches) == 2


def test_isolation_accepts_own_premises():
    """分支隔离门正例：引用本支私有前提的推导被接受
    （对照 Lean witness_own_accepted/derivation_wf_accepts）。"""
    _x, _y, bx, _by = _two_candidates_and_branches()
    d = R.BranchDerivation('d1', 'payment_due', frozenset({'mat-11'}))
    assert R.derivation_ok(bx, d)
    assert K.check_branch_isolation(bx, accepted=[d], rejected=[]).ok


def test_cross_branch_citation_rejected():
    """T123 原反例（独立保留）：引用另一支前提的推导被隔离门拒绝
    （对照 Lean witness_cross_rejected/witness_cross_not_wf/branch_isolation）。"""
    _x, _y, bx, by = _two_candidates_and_branches()
    cross = R.BranchDerivation('d-cross', 'payment_due',
                               frozenset({'mat-22'}))
    assert not R.derivation_ok(bx, cross)
    assert R.premises_disjoint(bx, by)
    assert K.check_cross_branch_rejection(bx, by, cross).ok
    assert K.check_branch_isolation(bx, accepted=[], rejected=[cross]).ok


# ---------------------------------------------------------------------------
# 独立 checker 差分
# ---------------------------------------------------------------------------


def test_checker_passes_witness_layer():
    x, y = _cand('c1'), _cand('c2', method=R.InterpMethod.SYSTEMATIC,
                              inp=INPUT_Y, rule=RULE_B)
    layer = R.build_interp_layer([x, y], (R.PriorityPair('c1', 'c2'),))
    report = K.check_interp_layer([x, y], (R.PriorityPair('c1', 'c2'),),
                                  layer)
    assert report.ok, report.reasons


def test_checker_rejects_forged_pool():
    """checker 独立重算采用池：伪造（把不可采用候选塞进池）被拒。"""
    x = _cand('c1')
    unauth = R.mk_literal('c2', INPUT_Y, 'art7', 'civil',
                          R.InterpEffect.SELECT_READING, RULE_B, 'reason-2')
    layer = R.build_interp_layer([x, unauth])
    forged = R.InterpLayer(
        pool=('c1', 'c2'), resolved=('c1', 'c2'), branches=layer.branches,
        attacks=layer.attacks, priorities_applied=(),
        referral=layer.referral, rule_base=layer.rule_base)
    report = K.check_interp_layer([x, unauth], (), forged)
    assert not report.ok and any('pool' in r for r in report.reasons)


def test_checker_rejects_forged_rule_base():
    """checker 独立核规则库纪律：无合法采用载体的规则进库被拒
    （未采用候选不进入无条件规则库）。"""
    x = _cand('c1')
    unauth = R.mk_literal('c2', INPUT_Y, 'art7', 'civil',
                          R.InterpEffect.SELECT_READING, RULE_B, 'reason-2')
    layer = R.build_interp_layer([x, unauth])
    forged = R.InterpLayer(
        pool=layer.pool, resolved=layer.resolved, branches=layer.branches,
        attacks=layer.attacks, priorities_applied=(),
        referral=layer.referral, rule_base=frozenset({RULE_A, RULE_B}))
    report = K.check_interp_layer([x, unauth], (), forged)
    assert not report.ok and any('rule base' in r for r in report.reasons)


def test_checker_rejects_merged_branches():
    """checker 独立核支路保留：两候选被并成一支支路被拒（不合并、不丢弃）。"""
    x, y = _cand('c1'), _cand('c2', method=R.InterpMethod.SYSTEMATIC,
                              inp=INPUT_Y, rule=RULE_B)
    layer = R.build_interp_layer([x, y])
    merged = R.InterpBranch(branch_id='c1',
                            adopted=frozenset({'c1', 'c2'}),
                            private_premises=frozenset({'mat-11', 'mat-22'}))
    forged = R.InterpLayer(
        pool=layer.pool, resolved=layer.resolved, branches=(merged,),
        attacks=layer.attacks, priorities_applied=(),
        referral=layer.referral, rule_base=layer.rule_base)
    report = K.check_interp_layer([x, y], (), forged)
    assert not report.ok and any('branch' in r for r in report.reasons)


def test_checker_rejects_reported_accepted_foreign():
    """checker 核隔离门：把跨支推导报成"已接受"被拒。"""
    _x, _y, bx, _by = _two_candidates_and_branches()
    cross = R.BranchDerivation('d-cross', 'payment_due',
                               frozenset({'mat-22'}))
    report = K.check_branch_isolation(bx, accepted=[cross], rejected=[])
    assert not report.ok and any('foreign' in r for r in report.reasons)


# ---------------------------------------------------------------------------
# 合成回执：completion/validate 六件套收口
# ---------------------------------------------------------------------------


def _lean_has(theorem: str) -> bool:
    local = theorem.split('.')[-1]
    text = LEAN_MODULE.read_text(encoding='utf-8')
    return f'theorem {local} ' in text


def _test_functions_of_this_module():
    tree = ast.parse(Path(__file__).read_text(encoding='utf-8'))
    return {node.name for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef) and
            node.name.startswith('test_')}


CONTRACT_NAME = 'JurisLean.Seams.UnifiedW4Interp'


def _receipt_row(t_id, theorem, test_ids, negative_ids):
    return {
        'id': t_id,
        'theorem': theorem,
        'contract': CONTRACT_NAME,
        'proof_mode': 'KERNEL_CONTRACT_PROOF',
        'generality': 'PARAMETRIC_OVER_FINITE_CANDIDATE_POOL',
        'formal_scope': 'five interpretation constructors over finite '
                        'candidate pools; branch layer over the adoptable '
                        'pool; isolation gate over finite premise lists',
        'independent_semantics': 'interp_ref_check.py inline re-derivation '
                                 '(adoptable/conflict/priority/resolution/'
                                 'isolation), shares frozen carriers only',
        'algorithm': 'interpretation_ref.py mk_* constructors, rule_base, '
                     'branch_each, resolved_by_priority, derivation_ok',
        'observation_contract': 'InterpLayer (pool/resolved/branches/attacks/'
                                'priorities/referral/rule_base) + '
                                'derivation_ok per branch derivation',
        'external_assumptions': 'synthetic sources only; no real statute '
                                'force is asserted (法源标签为合成登记值)',
        'proof_sources': ['proofs/lean/juris_lean/JurisLean/Seams/'
                          'UnifiedW4Interp.lean'],
        'implementation_sources': [
            'tools/full_math/implementation/interpretation_ref.py',
            'tools/full_math/implementation/interp_ref_check.py',
            'tools/unified_math_v2/unified/pipeline.py',
        ],
        'test_ids': test_ids,
        'negative_test_ids': negative_ids,
        'semantic_links': ['JurisLean.Seams.UnifiedW4Interp'],
    }


T122_THEOREM = ('JurisLean.Seams.UnifiedW4Interp.'
                'method_use_not_proof_of_correctness')
T123_THEOREM = 'JurisLean.Seams.UnifiedW4Interp.branch_isolation'


def test_completion_receipt_t122():
    row = _receipt_row(
        'W4:T122', T122_THEOREM,
        ['tools/full_math/implementation_tests/test_interpretation_ref.py::'
         'test_constructor_preserves_input_face',
         'tools/full_math/implementation_tests/test_interpretation_ref.py::'
         'test_rule_base_only_adopted'],
        ['tools/full_math/implementation_tests/test_interpretation_ref.py::'
         'test_method_use_not_proof_of_correctness'])
    C.validate_binding(row, {'id': row['id'], 'theorem': T122_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_t123():
    row = _receipt_row(
        'W4:T123', T123_THEOREM,
        ['tools/full_math/implementation_tests/test_interpretation_ref.py::'
         'test_isolation_accepts_own_premises',
         'tools/unified_math_v2/tests/test_interpretation_branch.py::'
         'test_run_case_attaches_interp_layer'],
        ['tools/full_math/implementation_tests/test_interpretation_ref.py::'
         'test_cross_branch_citation_rejected'])
    C.validate_binding(row, {'id': row['id'], 'theorem': T123_THEOREM,
                             'contract': row['contract']}, repo=REPO)


def test_completion_receipt_negative_tampered():
    row = _receipt_row('W4:T122', T122_THEOREM,
                       ['tools/full_math/implementation_tests/'
                        'test_interpretation_ref.py::'
                        'test_constructor_preserves_input_face'],
                       ['tools/full_math/implementation_tests/'
                        'test_interpretation_ref.py::'
                        'test_method_use_not_proof_of_correctness'])
    row['proof_mode'] = 'FIXED_EXAMPLE_NOT_PROOF'
    with pytest.raises(C.EvidenceError):
        C.validate_binding(row, {'id': row['id'], 'theorem': T122_THEOREM,
                                 'contract': row['contract']})


def test_receipt_anchors_resolve():
    """回执锚点实盘：引用的 Lean 定理与本模块测试节点都真实存在。"""
    assert _lean_has(T122_THEOREM)
    assert _lean_has(T123_THEOREM)
    tests = _test_functions_of_this_module()
    for name in ('test_constructor_preserves_input_face',
                 'test_rule_base_only_adopted',
                 'test_method_use_not_proof_of_correctness',
                 'test_isolation_accepts_own_premises',
                 'test_cross_branch_citation_rejected'):
        assert name in tests
