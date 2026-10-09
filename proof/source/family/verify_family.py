# Exhaustive independent finite-field checks of the proposed family for e=1..6.
# Fields use irreducible polynomials listed below, validated by inversion of
# every nonzero field element (via a simple multiplication search).
polys={1:0b11,2:0b111,3:0b1011,4:0b10011,5:0b100101,6:0b1000011}
V=[sum(((a&m).bit_count()%2)<<i for i,m in enumerate([3,1,4,8,2,3])) for a in range(16)]
Uodd=[0,19,33,50];Ueven=[0,12,22,26]
for e,mod in polys.items():
 def mul(a,b):
  r=0
  while b:
   if b&1:r^=a
   b>>=1;a<<=1
   if a>>e:a^=mod
  return r
 assert all(any(mul(a,b)==1 for b in range(1,1<<e)) for a in range(1,1<<e))
 singular=[]
 for label in range(1<<(2*e+2)):
  coeff=[V[label&15]]
  for j in range(1,e):coeff.append((Uodd if j%2 else Ueven)[(label>>(2*j+2))&3])
  edges=[sum(((c>>k)&1)<<j for j,c in enumerate(coeff)) for k in range(6)]
  pf=mul(edges[0],edges[5])^mul(edges[1],edges[4])^mul(edges[2],edges[3])
  if not pf:singular.append(label)
 assert singular==[0,4,8,13,14,15]
 print(f'e={e}, n={4*e}, parameters={1<<(2*e+2)}, singular={singular}, nonzero_nonbent={6*(1<<(2*e-2))-1}',flush=True)
