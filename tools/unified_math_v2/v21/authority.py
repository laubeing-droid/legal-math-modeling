"""Reuse host trust, do not build a new PKI. Local analysis works with no keys.

This reference represents a trusted host's ALREADY verified record store.
Populating it from arbitrary input is outside the trust boundary and prohibited.
Local records never represent an external institution's endorsement.
"""
from dataclasses import dataclass
from types import MappingProxyType
from .context import ContextKey


@dataclass(frozen=True)
class AuthorityRecord:
    record_id: str
    context: ContextKey
    issuer: str
    use: str
    content_ref: str
    valid_from: str
    valid_through: str
    evidence_class: str
    revoked: bool = False

    def __post_init__(self):
        if not all((self.record_id,self.issuer,self.use,self.content_ref)):
            raise ValueError('Incomplete host record')
        from datetime import date
        if date.fromisoformat(self.valid_from)>date.fromisoformat(self.valid_through):
            raise ValueError('Invalid authority validity interval')
        if self.evidence_class not in {'local_record','institutional_source_verified','synthetic'}:
            raise ValueError('Unknown host evidence class')


class ExistingHostRecords:
    """Trusted dependency created by the host, never deserialized from a case bundle."""
    def __init__(self, records=()):
        records=tuple(records)
        if any(type(r) is not AuthorityRecord for r in records): raise TypeError('Host records required')
        if len({r.record_id for r in records})!=len(records): raise ValueError('Duplicate record id')
        self._records=MappingProxyType({r.record_id:r for r in records})

    def authorizes(self, record_id, context, use, content_ref, at_date):
        from datetime import date
        at=date.fromisoformat(at_date)
        r=self._records.get(record_id)
        return bool(r and r.context==context and r.use==use and r.content_ref==content_ref
                    and not r.revoked and date.fromisoformat(r.valid_from)<=at<=date.fromisoformat(r.valid_through)
                    and r.evidence_class=='institutional_source_verified')


def institutional_projection(host, *, context, record_id, content_ref, at_date):
    if type(host) is not ExistingHostRecords:
        raise TypeError('Existing trusted host resolver required')
    if not host.authorizes(record_id,context,'institutional_finding',content_ref,at_date):
        return {'status':'pending_institutional_verification','fact_promotions':0}
    return {'status':'recorded_institutional_finding','record_id':record_id,
            'scope':'verified_source_record_only','fact_promotions':0}


def local_analysis_projection(context, assumptions):
    if tuple(sorted(assumptions))!=context.assumptions: raise ValueError('Unbound assumptions')
    return {'status':'conditional_analysis','signature_status':'not_used',
            'assumptions':context.assumptions,'fact_promotions':0}
