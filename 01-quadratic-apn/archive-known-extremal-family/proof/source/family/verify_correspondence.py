#!/usr/bin/env python3
"""Exact binary congruence and finite determinant-fibre checks; no dependencies."""
from itertools import product, combinations
import json
PAIRS=list(combinations(range(4),2))
P=[[1,1,1,0],[0,1,1,1],[1,0,1,0],[0,1,0,1]]
def parity(n): return n.bit_count()&1
def mat(mask):
    a=[[0]*4 for _ in range(4)]
    for k,(i,j) in enumerate(PAIRS): a[i][j]=a[j][i]=(mask>>k)&1
    return a
def congr(mask):
    a=mat(mask)
    b=[[sum(P[k][i]*a[k][l]*P[l][j] for k in range(4) for l in range(4))%2 for j in range(4)] for i in range(4)]
    assert all(b[i][i]==0 for i in range(4))
    return sum(b[i][j]<<k for k,(i,j) in enumerate(PAIRS))
def pf(m): return ((m&1)*((m>>5)&1)) ^ (((m>>1)&1)*((m>>4)&1)) ^ (((m>>2)&1)*((m>>3)&1))
assert len({tuple(sum(P[i][j]*((v>>j)&1) for j in range(4))%2 for i in range(4)) for v in range(16)})==16
assert len({congr(v) for v in range(64)})==64
assert all(pf(v)==pf(congr(v)) for v in range(64))
assert [congr(v) for v in [12,22,19,33,47,61]]==[18,28,22,26,1,32]
for u,v,w,z in product(range(2),repeat=4):
    a=(u^v)|(u<<1)|(w<<2)|(z<<3)|(v<<4)|((u^v)<<5)
    x,y,h0,h1=u^w^z,v^w^z,u^v^z,w^z
    expected=x^(y<<5)^(18 if h0 else 0)^(28 if h1 else 0)
    assert congr(a)==expected
I=(1,0,0,1);R=(0,1,1,1);J=(1,1,0,1)
def mm(a,b): return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%2 for i in range(2) for j in range(2))
def xor(a,b): return tuple(x^y for x,y in zip(a,b))
assert mm(J,J)==I and xor(xor(mm(R,R),R),I)==(0,0,0,0)
assert mm(J,R)==mm(mm(R,R),J)
assert len({tuple(parity(sum((m[k]<<j) for j,m in enumerate([I,R,J,mm(J,R)]))&a) for k in range(4)) for a in range(16)})==16
polys={1:0b11,2:0b111,3:0b1011,4:0b10011,5:0b100101,6:0b1000011}
results=[]
for e,mod in polys.items():
    def mul(a,b):
        out=0
        while b:
            if b&1:out^=a
            a<<=1;b>>=1
            if a>>e:a^=mod
        return out
    K=[(0,0,0,0),I,R,xor(I,R)]
    zero=[];one=[];images=set()
    for label in range(1<<(2*e)):
        B=[0]*4
        for j in range(e):
            C=K[(label>>(2*j))&3]
            if j%2:C=mm(J,C)
            for k in range(4): B[k]^=C[k]<<j
        images.add(tuple(B))
        d=mul(B[0],B[3])^mul(B[1],B[2])
        if d==0:zero.append(label)
        if d==1:one.append(label)
    assert len(images)==1<<(2*e) and zero==[0] and one==[1,2,3]
    results.append({'e':e,'core_dimension':2*e,'core_parameters':len(images),'det_zero_labels':zero,'det_one_labels':one,'singular_augmented_pencil':6})
print(json.dumps({'verified':True,'binary_congruence_inputs':64,'base_parameter_inputs':16,'field_checks':results},indent=2))
