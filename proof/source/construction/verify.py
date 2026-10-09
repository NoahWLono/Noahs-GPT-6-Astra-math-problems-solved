import json
# Independent polynomial-convolution field arithmetic, modulus t^3+t+1.
def mul(x,y):
 p=0
 for i in range(3):
  for j in range(3):
   if (x>>i)&(y>>j)&1:p^=1<<(i+j)
 for i in range(4,2,-1):
  if p>>i&1:p^=11<<(i-3)
 return p
def power(x,n):
 r=1
 for _ in range(n):r=mul(r,x)
 return r
def trace(x):
 r=x^power(x,2)^power(x,4)
 assert r in (0,1)
 return r
def rank(m,q):
 m=[r[:] for r in m];nr=len(m);nc=len(m[0]);r=0
 for c in range(nc):
  p=next((i for i in range(r,nr) if m[i][c]),None)
  if p is None:continue
  m[r],m[p]=m[p],m[r]
  if q==8:
   inv=power(m[r][c],6)
   m[r]=[mul(x,inv) for x in m[r]]
  for i in range(nr):
   if i!=r and m[i][c]:
    fac=m[i][c]
    m[i]=[x^(mul(fac,y) if q==8 else y) for x,y in zip(m[i],m[r])]
  r+=1
 return r
pairs=[(i,j) for i in range(4) for j in range(i+1,4)]
v=[sum(((a&m).bit_count()%2)<<i for i,m in enumerate([3,1,4,8,2,3])) for a in range(16)]
bs=[0,19,33,50];cs=[0,12,22,26]
def matrix(a,b,c):
 m=[[0]*4 for _ in range(4)]
 for bit,(i,j) in enumerate(pairs):m[i][j]=m[j][i]=((a>>bit)&1)|(((b>>bit)&1)<<1)|(((c>>bit)&1)<<2)
 return m
def lift(m):
 return [[trace(mul(mul(1<<(i%3),m[i//3][j//3]),1<<(j%3))) for j in range(12)] for i in range(12)]
basis=[lift(matrix(v[1<<k],0,0)) for k in range(4)]+[lift(matrix(0,b,0)) for b in [19,33]]+[lift(matrix(0,0,c)) for c in [12,22]]
hist8={};hist2={};singular=[]
for label in range(256):
 a=label&15;b=(label>>4)&3;c=(label>>6)&3
 m=matrix(v[a],bs[b],cs[c]);r8=rank(m,8);n=lift(m);r2=rank(n,2)
 assert r2==3*r8
 recomposed=[[0]*12 for _ in range(12)]
 for k in range(8):
  if label>>k&1:
   for i in range(12):
    for j in range(12):recomposed[i][j]^=basis[k][i][j]
 assert n==recomposed
 hist8[r8]=hist8.get(r8,0)+1;hist2[r2]=hist2.get(r2,0)+1
 if r2<12:singular.append(label)
assert singular==[0,4,8,13,14,15]
lexpairs=[(i,j) for i in range(12) for j in range(i+1,12)]
masks=[sum(basis[k][i][j]<<k for k in range(8)) for i,j in lexpairs]
assert rank([[basis[k][i][j] for i,j in lexpairs] for k in range(8)],2)==8
certificate={'field_modulus':'t^3+t+1','input_order':'x0 bits (1,t,t^2), x1 bits, x2 bits, x3 bits','output_bits':8,'zero_padding_output_bits':4,'coordinate_masks_lex_pairs':masks,'basis_matrices':basis,'singular_effective_labels':singular,'gf8_rank_histogram':hist8,'binary_rank_histogram':hist2,'nonzero_nonbent_12_output':6*16-1}
with open('sharpness-scalar-extension/gf8/certificate.json','w') as f:json.dump(certificate,f,indent=2)
print('GF8 rank histogram:',hist8)
print('Trace binary rank histogram:',hist2)
print('Singular effective labels:',singular)
print('66 coefficient masks:',masks)
print('Independent GF8 elimination, binary trace elimination, linearity, and dimension8 verified.')
