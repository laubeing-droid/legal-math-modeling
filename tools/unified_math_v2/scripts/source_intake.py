#!/usr/bin/env python3
"""Capture existing local source bytes with exact provenance; never legal approval.
Use LCCC's source acquisition first. No OCR, no model-derived substitute, no
client data in public CI. A URL name alone cannot mark a text authoritative.
"""
import argparse,hashlib,json
from pathlib import Path
from urllib.parse import urlparse
ROOT=Path(__file__).resolve().parents[1]
def capture(source_id,local_file,origin_url,output):
    registry=json.loads((ROOT/'manifests/sources.json').read_text(encoding='utf-8'))['sources']
    entries=[r for r in registry if r['id']==source_id]
    if len(entries)!=1:raise ValueError('Unknown source ID')
    entry=entries[0]
    if urlparse(origin_url).scheme!='https' or urlparse(origin_url).hostname!=urlparse(entry['url']).hostname:
        raise ValueError('Source host mismatch; review redirected source registration first')
    data=local_file.read_bytes()
    if not data or len(data)>20_000_000:raise ValueError('Empty/oversized source')
    data.decode('utf-8')
    h=hashlib.sha256(data).hexdigest();output.mkdir(parents=True,exist_ok=True)
    target=output/(h+'.source.txt')
    if target.exists() and target.read_bytes()!=data:raise ValueError('Content collision')
    target.write_bytes(data)
    report={'source_id':source_id,'registered_url':entry['url'],'actual_origin_url':origin_url,
      'sha256':h,'local_object':target.name,'scope':'BYTES_CAPTURED_ONLY',
      'fulltext_authenticity':'REQUIRES_VERIFICATION','translation_approval':'NOT_GRANTED',
      'applicability':'NOT_DETERMINED'}
    (output/(h+'.record.json')).write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    return report
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source-id',required=True);p.add_argument('--local-file',type=Path,required=True)
    p.add_argument('--origin-url',required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    print(json.dumps(capture(a.source_id,a.local_file,a.origin_url,a.output),ensure_ascii=False,indent=2))
