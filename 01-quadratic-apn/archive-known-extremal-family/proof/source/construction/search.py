from itertools import combinations
# Lex pairs 01,02,03,12,13,23. Output coefficient masks.
masks=[3,1,4,8,2,3]
V=[sum(((a&m).bit_count()%2)<<i for i,m in enumerate(masks)) for a in range(16)]
def mul(a,b):
 r=0
 while b:
  if b&1:r^=a
  a<<=1;b>>=1
  if a&8:a^=11
 return r
def pf(a,b,c):
 e=[((a>>i)&1)|(((b>>i)&1)<<1)|(((c>>i)&1)<<2) for i in range(6)]
 return mul(e[0],e[5])^mul(e[1],e[4])^mul(e[2],e[3])
good={(b,c) for b in range(64) for c in range(64) if any((b,c)) and all(pf(a,b,c) for a in V)}
bgood=[b for b in range(1,64) if (b,0) in good]
cgood=[c for c in range(1,64) if (0,c) in good]
def spaces(g):
 return sorted({tuple(sorted([a,b,a^b])) for a,b in combinations(g,2) if a^b in g})
Bs=spaces(bgood); Cs=spaces(cgood)
print('V',V,'singular labels',[i for i,a in enumerate(V) if not pf(a,0,0)],flush=True)
print('good pair count',len(good),'B good',len(bgood),'C good',len(cgood),'B spaces',len(Bs),'C spaces',len(Cs),flush=True)
for B in Bs:
 for C in Cs:
  if all((b,c) in good for b in B for c in C):
   print('FOUND',B,C,flush=True);raise SystemExit
print('No product-space construction for this V.')
