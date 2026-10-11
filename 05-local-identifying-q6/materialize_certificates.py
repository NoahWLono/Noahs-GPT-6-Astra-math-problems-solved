"""Decompress the supplied certificates only after exact compressed/uncompressed checks."""
from pathlib import Path
import gzip,hashlib,json
p=Path(__file__).resolve().parent
for item in json.loads((p/'CERTIFICATES.json').read_text()):
 zipped=(p/item['gzip_path']).read_bytes()
 if len(zipped)!=item['gzip_bytes'] or hashlib.sha256(zipped).hexdigest()!=item['gzip_sha256']: raise SystemExit('Compressed certificate mismatch')
 raw=gzip.decompress(zipped)
 if len(raw)!=item['bytes'] or hashlib.sha256(raw).hexdigest()!=item['sha256']: raise SystemExit('Uncompressed certificate mismatch')
 target=p/item['path']
 if target.exists():
  if target.read_bytes()!=raw: raise SystemExit('Existing certificate differs; refusing overwrite')
 else:target.write_bytes(raw)
 print(item['path']+': exact SHA-256 verified')
