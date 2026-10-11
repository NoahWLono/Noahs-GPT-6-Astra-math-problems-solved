#!/usr/bin/env python3
"""Optional exact symbolic checks. Requires SymPy. No network operations."""
import json
from pathlib import Path
import sympy as s

x,y,u,v,z,a,b=s.symbols('x y u v z a b')
Fx=x**3+a*x+b
Fu=u**3+a*u+b
D=(x-u)**2
B=(x+u)*(x*u+a)+2*b
addition_num=(y-v)**2-(x+u)*D
residue=s.expand(addition_num-(B-2*v*y)).subs(y**2,Fx).subs(v**2,Fu)
assert s.expand(residue)==0
S3=D*z**2-2*B*z+(x*u-a)**2-4*b*(x+u)
assert s.expand(((D*z-B)**2-4*Fu*Fx)-D*S3)==0
# Global degree-three control E: y^2=x^3+1, G=(0,1).
xprime=(y-1)**2/x**2-x
yprime=(y-1)/x*(x-xprime)-y
control=s.together(yprime-(y-3)/(y+1))
num=s.fraction(control)[0]
assert s.rem(s.Poly(num,y),s.Poly(y**2-x**3-1,y)).is_zero
# Denominator-cleared sharpness equality R(x)=x/(x+5) on E/F_11.
Bs=B.subs({u:2,a:1,b:6})
K=s.expand(Bs*(x+5)-x*(x-2)**2)
raw=s.expand(K**2-4*16*(x+5)**2*(x**3+x+6))
expected=(x-3)*(x-2)**3*(x+1)*(x+4)
assert s.Poly(raw-expected,x,modulus=11).is_zero
# Degree-four x-only doubling map exists: changing translation to [2] is not allowed.
L=((3*x*x+a)**2-8*x*(x**3+a*x+b))
L=s.expand(L)
assert L == x**4-2*a*x*x-8*b*x+a*a
report={'status':'PASS','sympy_version':s.__version__,
        'general_addition_numerator_identity':True,
        'semaev_biquadratic_factorization_identity':True,
        'global_degree_three_translation_identity':True,
        'sharpness_raw_eliminant_mod_11':str(s.factor(raw,modulus=11)),
        'raw_eliminant_warning':'Contains a removable (x-2)^2 factor; affine clearing is not proof at P=G.',
        'doubling_rational_map_numerator':str(L),
        'formal_proof_assistant_used':False}
root=Path(__file__).resolve().parents[1]
(root/'results/symbolic_checks.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
