import json,itertools,collections,numpy as np,hashlib,time
cert=json.load(open('sharpness-scalar-extension/gf8/certificate.json'))
masks=cert['coordinate_masks_lex_pairs'];pairs=list(itertools.combinations(range(12),2))
N=4096
f=[]
for x in range(N):
 y=0
 for (i,j),a in zip(pairs,masks):
  if ((x>>i)&1) and ((x>>j)&1):y^=a
 f.append(y)
def mul(a,b):
 z=0
 while b:
  if b&1:z^=a
  b>>=1;a<<=1
  if a&8:a^=11
 return z
def trace(a):return a ^ mul(a,a) ^ mul(mul(a,a),mul(a,a))
def entries(b):
 u,v,w,z,s,t,p,q=[(b>>i)&1 for i in range(8)]
 return [u^v^mul(2,s^t),u^mul(2,s)^mul(4,q),w^mul(4,p^q),z^mul(4,p),v^mul(2,s)^mul(4,q),u^v^mul(2,t)]
gpairs=list(itertools.combinations(range(4),2))
for x in range(N):
 xx=[(x>>(3*i))&7 for i in range(4)]; y=0
 for b in range(8):
  value=0
  for (i,j),a in zip(gpairs,entries(1<<b)):value^=mul(a,mul(xx[i],xx[j]))
  bit=trace(value);assert bit in (0,1)
  y|=bit<<b
 assert y==f[x],(x,y,f[x])
par=np.array([i.bit_count()%2 for i in range(256)],dtype=np.int64);fa=np.array(f,dtype=np.int64)
counts={};bad=[];amplitudes=collections.Counter();spectra={}
for b in range(256):
 a=(1-2*par[fa&b]).copy();h=1
 while h<N:
  a=a.reshape(-1,2*h);left=a[:,:h].copy();right=a[:,h:].copy();a[:,:h]=left+right;a[:,h:]=left-right;a=a.reshape(-1);h*=2
 bent=bool(np.all(a*a==N))
 if not bent:bad.append(b)
 amp=int(np.max(np.abs(a)));amplitudes[amp]+=1
 spectra[b]={str(int(k)):int(v) for k,v in zip(*np.unique(a,return_counts=True))}
 # Check a few raw Walsh coefficients against independently computed signs.
 for u in [0,1,7,83,1023,4095]:
  w=sum(1-2*((((b&f[x]).bit_count())+((u&x).bit_count()))%2) for x in range(N))
  assert w==int(a[u]),(b,u,w,a[u])
assert bad==[0,4,8,13,14,15],bad
assert amplitudes=={4096:1,64:250,512:5},amplitudes
out={'input_bits':12,'effective_output_bits':8,'bad_effective_masks':bad,'amplitudes_including_zero':dict(amplitudes),'padded_nonzero_nonbent':len(bad)*16-1,'truth_table_sha256':hashlib.sha256(bytes(f)).hexdigest(),'spectra':spectra}
json.dump(out,open('n12-independent/verification.json','w'),indent=2);json.dump(f,open('n12-independent/truth-table.json','w'))
print('PASS', {k:v for k,v in out.items() if k!='spectra'})
