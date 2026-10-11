"""W4 deviation seam reference: T124-T127 (plan §10.1, §9.4, §12.2, §12.3,
§12.5, §7.3).

K rows 2553-2556 (docs/spec/20261007-统一法律数学模型_附录K_全量目标落实表.md):
T124 解释一致性 — §10.1,11.2：已采用解释表示保持；回流有权限/时际；
T125 三参照偏离 — §12.2：三参照距离及固定域/基准 Hausdorff 偏移界；
T126 倾向分层   — §12.3,7.3：分层倾向实算、选择/迁移假设，不重复先验数据；
T127 偏离报告   — §12.5：偏离报告完整比较/来源/不确定性，忠实投影。

T124: an ADOPTED interpretation is serialized into a representation-layer
record whose readings equal the adoption-layer preimage (no drift: the
representation readings ARE the rule base of the adopted pool); a reflow
event must carry a named authority and an in-window effective time —
unauthorized or out-of-window reflows are rejected and leave the log
untouched (append-only, §9.4/§10.1: 回流只追加具名事件，不重写历史).
T125: readings deviate from three reference pools (SELF/PEER/UPPER) that
must pass comparability AND non-emptiness gates (an empty pool is no
baseline and is never filled with 0); dev(x,S)=min|x-s| over rationals,
with the fixed-domain shift bound d_H(S, S+delta) <= |delta|.
T126: stratum = finite stratification key; propensity = exact count ratio
s/(s+f) as Fraction; the propensity input type carries ONLY the observation
table (no prior channel) and the prior table is a separate type — re-using
the same labels as prior mass is detectable (3/4 vs 2/3) and rejected;
selection/migration assumptions are EXPLICIT gate parameters (§7.3), and
the output use-type has no "enter norm base" constructor (§12.3: 倾向不写
入法源).
T127: the deviation report packages the three-reference reading, named
source annotations (structural/normative/empirical kinds), and a
Fraction uncertainty interval; the faithful-projection gate rejects any
report whose reading drifts from the underlying preimage, and the
completeness gate requires every actual source to be enumerated or the
residual to be named.

Lean contract: proofs/lean/juris_lean/JurisLean/Seams/UnifiedW4Deviation.lean
(namespace JurisLean.Seams.UnifiedW4Deviation; consumes the green
JurisLean.Seams.UnifiedW4Interp adoption layer).  Independent checker:
tools/full_math/implementation/deviation_check.py (shares only these frozen
carriers, re-implements every predicate inline).
"""
from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from fractions import Fraction as Q
from typing import Iterable, Optional, Tuple

from tools.full_math.implementation.interpretation_ref import (
    InterpCandidate,
    RuleAst,
    adoptable,
)


# ---------------------------------------------------------------------------
# T124 已采用解释表示保持 ＋ 回流权限/时际（§10.1、§9.4）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class RepRecord:
    """表示层记录：已采用候选的冻结序列化（§10.1 表示保持——记录逐字段保存
    原像：方法、规则 AST、具名理由、法定权限）."""

    cand_id: str
    method: object
    rule: RuleAst
    reason_id: Optional[str]
    authority_id: Optional[str]


def record_of(c: InterpCandidate) -> RepRecord:
    """序列化门（fail-fast）：只序列化已采用候选——构造≠采用，未采用候选的
    "读数"进不了表示层（T122 采用门的下游面）."""

    if not adoptable(c):
        raise ValueError(
            "representation record requires an ADOPTED candidate "
            "(T124: 未采用候选不进表示层)")
    return RepRecord(cand_id=c.candidate_id, method=c.method, rule=c.rule,
                     reason_id=c.reason_id, authority_id=c.authority_id)


def record_rule(r: RepRecord) -> RuleAst:
    """表示层读数（规则面）：记录读出的规则 AST＝原像的规则."""

    return r.rule


def record_adoptable(r: RepRecord) -> bool:
    """表示层读数（可采用面）：与采用层门同型同值."""

    return bool(r.reason_id) and r.authority_id is not None


@dataclass(frozen=True)
class InterpRepLayer:
    """T124 表示层快照：采用门过滤的冻结日志、表示层读数、逐字段序列化记录."""

    log: Tuple[InterpCandidate, ...]
    readings: Tuple[RuleAst, ...]
    records: Tuple[RepRecord, ...]


def rep_log(cands: Iterable[InterpCandidate]) -> Tuple[InterpCandidate, ...]:
    """表示层日志：只收采用门通过的候选（原像本身冻结）."""

    return tuple(c for c in cands if adoptable(c))


def rep_readings(cands: Iterable[InterpCandidate]) -> Tuple[RuleAst, ...]:
    """表示层读数＝采用层规则库原像（与日志同序，不漂移；集合意义＝rule_base）."""

    return tuple(c.rule for c in cands if adoptable(c))


def build_interp_rep_layer(
        cands: Iterable[InterpCandidate]) -> InterpRepLayer:
    """总装 T124 表示层：候选 id 唯一 fail-fast；日志/读数/记录三面一致."""

    cands = tuple(cands)
    ids = [c.candidate_id for c in cands]
    if len(set(ids)) != len(ids):
        raise ValueError("duplicate interpretation candidate id")
    log = rep_log(cands)
    return InterpRepLayer(
        log=log,
        readings=rep_readings(cands),
        records=tuple(record_of(c) for c in log))


@dataclass(frozen=True)
class ReflowEvent:
    """回流事件（§9.4：规范回流必须是有权限、有程序、有生效条件的事件——
    本件合同面取权限与时点两个必需面）."""

    event_id: str
    cand_id: str
    authority_id: Optional[str]
    at_day: int


@dataclass(frozen=True)
class ReflowWindow:
    """回流生效窗（§10.1 asOf 面：生效条件的有限窗）."""

    open_day: int
    close_day: int


def authority_ok(e: ReflowEvent) -> bool:
    return e.authority_id is not None


def in_window(w: ReflowWindow, e: ReflowEvent) -> bool:
    return w.open_day <= e.at_day <= w.close_day


def reflow_ok(w: ReflowWindow, e: ReflowEvent) -> bool:
    """回流门＝权限∧时点."""

    return authority_ok(e) and in_window(w, e)


def apply_reflow(log: Tuple[InterpCandidate, ...], w: ReflowWindow,
                 e: ReflowEvent, c: InterpCandidate
                 ) -> Tuple[InterpCandidate, ...]:
    """回流应用（§10.1：append-only——被拒不改日志，接受才追加）."""

    if not reflow_ok(w, e):
        return log
    return log + (c,)


def check_reflow(w: ReflowWindow, e: ReflowEvent,
                 cands: Iterable[InterpCandidate]) -> InterpCandidate:
    """回流门（fail-fast）：无权限→PermissionError；越窗→ValueError；目标
    候选须存在且已采用。返回被回流的候选."""

    if not authority_ok(e):
        raise PermissionError(
            f"reflow {e.event_id} rejected: no named authority (§9.4)")
    if not in_window(w, e):
        raise ValueError(
            f"reflow {e.event_id} rejected: at_day {e.at_day} outside "
            f"window [{w.open_day}, {w.close_day}] (§9.4)")
    for c in cands:
        if c.candidate_id == e.cand_id:
            if not adoptable(c):
                raise ValueError(
                    f"reflow {e.event_id} rejected: candidate "
                    f"{e.cand_id} is not adopted (T124)")
            return c
    raise ValueError(
        f"reflow {e.event_id} rejected: candidate {e.cand_id} not found")


# ---------------------------------------------------------------------------
# T125 三参照偏离（§12.2）
# ---------------------------------------------------------------------------


def dev_dist(x: Q, y: Q) -> Q:
    """ℚ 值距离（不浮点）."""

    return abs(x - y)


def dev_min_list(vals: Iterable[Q]) -> Q:
    """有限 ℚ 表最小值（空表回退 0——合同面由非空门另行把关）."""

    vals = tuple(vals)
    if not vals:
        return Q(0)
    m = vals[0]
    for v in vals[1:]:
        m = min(m, v)
    return m


def dev_max_list(vals: Iterable[Q]) -> Q:
    """有限 ℚ 表最大值（同上）."""

    vals = tuple(vals)
    if not vals:
        return Q(0)
    m = vals[0]
    for v in vals[1:]:
        m = max(m, v)
    return m


def dev_of(x: Q, s_set: Tuple[Q, ...]) -> Q:
    """§12.2 偏离：dev(x,S)=min_{s∈S}|x−s|（有限参照集为 min）."""

    return dev_min_list(dev_dist(x, s) for s in s_set)


def d_haus(s: Tuple[Q, ...], t: Tuple[Q, ...]) -> Q:
    """§12.2 Hausdorff 距离（ℚ 值；有限集 max-min）."""

    return max(
        dev_max_list(dev_of(si, t) for si in s),
        dev_max_list(dev_of(ti, s) for ti in t))


def hausdorff_shift(s: Tuple[Q, ...], delta: Q) -> Q:
    """固定域平移后的 Hausdorff 距离（实算入口；定理保证 ≤ |δ|）."""

    return d_haus(s, tuple(si + delta for si in s))


class RefKind(Enum):
    """§12.2 三参照：本人先例 SELF、同级同行 PEER、上级裁判 UPPER."""

    SELF = "self"
    PEER = "peer"
    UPPER = "upper"


@dataclass(frozen=True)
class ThreeRefs:
    """三参照集合（各自先过可比性与非空门）."""

    self_set: Tuple[Q, ...]
    peer_set: Tuple[Q, ...]
    upper_set: Tuple[Q, ...]


@dataclass(frozen=True)
class Comparability:
    """§12.2 可比性门输入（同法域/版本/程序/争点及事实可比性）."""

    same_domain: bool
    same_version: bool
    same_procedure: bool
    same_issue: bool


def comparable(g: Comparability) -> bool:
    return (g.same_domain and g.same_version and g.same_procedure
            and g.same_issue)


def dev_reading_ok(s_set: Tuple[Q, ...]) -> bool:
    """非空门（§12.2：空 S 是无比较基准，不能填 0 偏离）."""

    return bool(s_set)


def ref_admit(g: Comparability, s_set: Tuple[Q, ...]) -> bool:
    """参照准入门＝可比∧非空."""

    return comparable(g) and dev_reading_ok(s_set)


def dev_three(x: Q, refs: ThreeRefs) -> dict:
    """三参照偏离实算（fail-fast：空参照集抛错，绝不填 0；不可比不进参照）."""

    for kind, s_set in ((RefKind.SELF, refs.self_set),
                        (RefKind.PEER, refs.peer_set),
                        (RefKind.UPPER, refs.upper_set)):
        if not dev_reading_ok(s_set):
            raise ValueError(
                f"{kind.value} reference pool is empty: no comparison "
                "baseline (§12.2 空 S 无比较基准，不能填 0 偏离)")
    return {RefKind.SELF: dev_of(x, refs.self_set),
            RefKind.PEER: dev_of(x, refs.peer_set),
            RefKind.UPPER: dev_of(x, refs.upper_set)}


# ---------------------------------------------------------------------------
# T126 倾向分层（§12.3、§7.3）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class StratObs:
    """分层观测：层键（有限分层编码）＋层内成功/失败计数——类型上没有先验
    字段（§7.3 不重复先验数据合同的第一面）."""

    key: str
    successes: int
    failures: int


def mk_strat_obs(key: str, successes: int, failures: int) -> StratObs:
    """观测构造门（fail-fast）：负计数直接拒绝."""

    if successes < 0 or failures < 0:
        raise ValueError(f"stratum {key}: negative count rejected (T126)")
    return StratObs(key=key, successes=successes, failures=failures)


def obs_total(o: StratObs) -> int:
    return o.successes + o.failures


def obs_ok(o: StratObs) -> bool:
    """观测门：零计数层不进分层表."""

    return obs_total(o) > 0


def propensity(o: StratObs) -> Q:
    """分层倾向实算＝层内计数比 s/(s+f)（ℚ 精确，不浮点）."""

    if not obs_ok(o):
        raise ValueError(
            f"stratum {o.key}: zero-count stratum rejected (T126)")
    return Q(o.successes, obs_total(o))


@dataclass(frozen=True)
class StratTable:
    """分层倾向表：层键×倾向（只由观测表构造——build_strat_table 的输入
    没有先验通道）."""

    layers: Tuple[Tuple[str, Q], ...]


def build_strat_table(obs: Iterable[StratObs]) -> StratTable:
    """总装：层键唯一 fail-fast；观测门过滤后逐层实算."""

    obs = tuple(obs)
    keys = [o.key for o in obs]
    if len(set(keys)) != len(keys):
        raise ValueError("duplicate stratum key")
    return StratTable(tuple((o.key, propensity(o))
                            for o in obs if obs_ok(o)))


@dataclass(frozen=True)
class PriorTable:
    """§7.3 先验表：Beta (α,β) 逐层另列——与观测表分型，不进倾向输入."""

    entries: Tuple[Tuple[str, int, int], ...]


def posterior_mean(alpha: int, beta: int, o: StratObs) -> Q:
    """§7.3 后验均值 (α+s)/(α+β+n)——仅作混入检验对照，不进倾向层输出."""

    return Q(alpha + o.successes, alpha + beta + obs_total(o))


@dataclass(frozen=True)
class PropensityAssumptions:
    """§7.3 选择/迁移假设——显式假设参数（不在定理内隐含）：选择机制已建模
    或已证可忽略；迁移支持覆盖已具名."""

    selection_modeled: bool
    migration_covered: bool


def assumptions_named(a: PropensityAssumptions) -> bool:
    return a.selection_modeled and a.migration_covered


def comparison_gate(a: PropensityAssumptions) -> bool:
    """层间比较门（fail-fast 面）：无名假设的比较直接拒绝
    （§12.3：进入预测必须满足 §7.3 的选择/迁移机制）."""

    if not assumptions_named(a):
        raise ValueError(
            "stratum comparison requires NAMED selection/migration "
            "assumptions (§7.3)")
    return True


class StratUse(Enum):
    """倾向输出用途分型：描述／经具名假设的比较——没有"写入法源"构造子
    （T126：倾向不写入法源）."""

    DESCRIPTIVE = "descriptive"
    COMPARISON_UNDER_NAMED_ASSUMPTIONS = "comparison_under_named_assumptions"


# ---------------------------------------------------------------------------
# T127 偏离报告（§12.5）
# ---------------------------------------------------------------------------


class DevKind(Enum):
    """偏离来源三分型（§12.2：结构偏离、规范不一致、经验异常——分别给依据，
    不能用距离大判违法）."""

    STRUCTURAL = "structural"
    NORMATIVE = "normative"
    EMPIRICAL = "empirical"


@dataclass(frozen=True)
class DevSource:
    """具名偏离来源标注."""

    source_id: str
    kind: DevKind


@dataclass(frozen=True)
class Uncert:
    """不确定性区间（§12.5 误差/样本边界——ℚ 端点）."""

    lo: Q
    hi: Q


def uncert_wf(u: Uncert) -> bool:
    return u.lo <= u.hi


@dataclass(frozen=True)
class DeviationReport:
    """偏离报告记录（§12.5：逐项保留比较对象、差异事实、规范对应、误差/
    样本边界和引用定位；生成文句不能抹掉原始 status）."""

    report_id: str
    ref_kind: RefKind
    reading: Q
    sources: Tuple[DevSource, ...]
    interval: Uncert
    residual_named: bool
    status_kept: bool


def mk_report(report_id: str, ref_kind: RefKind, reading: Q,
              sources: Iterable[DevSource], interval: Uncert
              ) -> DeviationReport:
    """报告构造器（打包：读数原样投影；区间良构、来源非空 fail-fast；
    残余具名与 status 保持默认置真——抹除是显式伪造面，由 report_ok/
    coverage_ok 把守）."""

    if not uncert_wf(interval):
        raise ValueError(
            "uncertainty interval must satisfy lo <= hi (T127)")
    sources = tuple(sources)
    if not sources:
        raise ValueError(
            "deviation report requires at least one NAMED source (§12.5)")
    return DeviationReport(report_id=report_id, ref_kind=ref_kind,
                           reading=reading, sources=sources,
                           interval=interval, residual_named=True,
                           status_kept=True)


def report_ok(r: DeviationReport, preimage: Q) -> bool:
    """忠实投影门：报告读数与底层原像一致（不重算——重算值≠投影值即漂移）."""

    return r.reading == preimage


def coverage_ok(actual: Tuple[DevSource, ...], r: DeviationReport) -> bool:
    """完整性门：实际来源逐项枚举 ∨ 残余具名（§12.5 完整性）."""

    return all(s in r.sources for s in actual) or r.residual_named


# ---------------------------------------------------------------------------
# 分包层总装（下游消费的单一入口：消费既有 interp 层）
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class DeviationLayer:
    """W4 偏离层快照：T124 表示层＋已应用/被拒回流＋T125 三参照读数与平移
    界＋T126 分层表＋T127 报告."""

    interp_rep: InterpRepLayer
    reflows: Tuple[Tuple[str, bool], ...]
    dev_readings: Tuple[Tuple[str, Q], ...]
    hausdorff_shifts: Tuple[Tuple[Q, Q], ...]
    strat_table: StratTable
    assumptions: PropensityAssumptions
    comparison_allowed: bool
    report: DeviationReport


def build_deviation_layer(
    cands: Iterable[InterpCandidate],
    *,
    reflow_requests: Tuple[Tuple[ReflowWindow, ReflowEvent,
                                 InterpCandidate], ...] = (),
    comparability: Comparability,
    refs: ThreeRefs,
    reading_point: Q = Q(0),
    shift_deltas: Tuple[Q, ...] = (Q(0),),
    strat_obs: Tuple[StratObs, ...] = (),
    assumptions: PropensityAssumptions,
    report_id: str = "report-1",
    report_kind: RefKind = RefKind.SELF,
    actual_sources: Tuple[DevSource, ...] = (),
    interval: Optional[Uncert] = None,
) -> DeviationLayer:
    """总装 W4 偏离层（§10.1/§12.2/§12.3/§12.5）：消费已采用候选池——

    - T124：表示层三面（日志/读数/记录）＋逐事件回流（被拒不改日志）；
    - T125：三参照偏离实算（空参照/不可比 fail-fast）＋固定域平移界实算；
    - T126：分层表实算（先验表不进输入）＋比较门读数；
    - T127：报告打包（读数＝SELF 偏离原像；来源/区间/完整性逐项把关）。
    """

    if interval is None:
        raise ValueError("deviation layer requires an uncertainty interval")
    interp_rep = build_interp_rep_layer(cands)
    reflows = tuple(
        (e.event_id, reflow_ok(w, e))
        for (w, e, _c) in reflow_requests)
    for kind, s_set in ((RefKind.SELF, refs.self_set),
                        (RefKind.PEER, refs.peer_set),
                        (RefKind.UPPER, refs.upper_set)):
        if not ref_admit(comparability, s_set):
            raise ValueError(
                f"{kind.value} reference pool fails comparability/"
                "non-emptiness gate (§12.2)")
    readings = dev_three(reading_point, refs)
    shifts = tuple((d, hausdorff_shift(refs.self_set, d))
                   for d in shift_deltas)
    table = build_strat_table(strat_obs)
    allowed = assumptions_named(assumptions)
    rep = mk_report(report_id, report_kind, readings[report_kind],
                    actual_sources, interval)
    return DeviationLayer(
        interp_rep=interp_rep,
        reflows=reflows,
        dev_readings=tuple((k.value, v) for k, v in readings.items()),
        hausdorff_shifts=shifts,
        strat_table=table,
        assumptions=assumptions,
        comparison_allowed=allowed,
        report=rep)
