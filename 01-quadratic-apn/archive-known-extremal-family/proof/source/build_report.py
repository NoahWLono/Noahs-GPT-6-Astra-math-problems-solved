#!/usr/bin/env python3
"""Build a readable PDF from the checked n=12 witness and certificate status.

Requires reportlab. All fonts are bundled. The script deliberately labels
an uncertified build as a working draft and does not invent Lean results.
"""
from pathlib import Path
from xml.sax.saxutils import escape
from itertools import combinations
import json, hashlib
from reportlab.lib import colors
from reportlab.lib.enums import TA_LEFT, TA_CENTER
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, PageBreak, Table, TableStyle, Preformatted, KeepTogether

ROOT=Path(__file__).resolve().parent
OUT=ROOT.parent/'output/pdf/gpt6_astra_extremal_quadratic_family.pdf'
CERT=json.loads((ROOT/'construction/certificate.json').read_text())
DATA=json.loads((ROOT/'results/reproduced.json').read_text())
STATUS=json.loads((ROOT/'certificate_status.json').read_text())
assert DATA['verified'] and DATA['nonzero_nonbent_masks']==95
for name,file in [('Serif','DejaVuSerif.ttf'),('SerifBold','DejaVuSerif-Bold.ttf'),('SerifItalic','DejaVuSerif-Italic.ttf'),('Sans','DejaVuSans.ttf'),('SansBold','DejaVuSans-Bold.ttf'),('Mono','DejaVuSansMono.ttf')]:
    pdfmetrics.registerFont(TTFont(name,str(ROOT/'fonts'/file)))
pdfmetrics.registerFontFamily('Serif',normal='Serif',bold='SerifBold',italic='SerifItalic',boldItalic='SerifBold')
pdfmetrics.registerFontFamily('Sans',normal='Sans',bold='SansBold',italic='Sans',boldItalic='SansBold')
styles=getSampleStyleSheet()
for name,opts in {
 'TitleR':dict(fontName='SerifBold',fontSize=25,leading=30,spaceAfter=14),
 'Label':dict(fontName='SansBold',fontSize=10,leading=14,spaceAfter=15),
 'Deck':dict(fontName='Serif',fontSize=12.3,leading=17.5,spaceAfter=17),
 'H':dict(fontName='SerifBold',fontSize=15,leading=20,spaceBefore=8,spaceAfter=10,keepWithNext=True),
 'H2':dict(fontName='SerifBold',fontSize=11.1,leading=15,spaceBefore=8,spaceAfter=6,keepWithNext=True),
 'BodyR':dict(fontName='Serif',fontSize=10.1,leading=14.6,spaceAfter=8),
 'SmallR':dict(fontName='Serif',fontSize=8.8,leading=12.4,spaceAfter=7),
 'Equation':dict(fontName='Serif',fontSize=10.9,leading=17,alignment=TA_CENTER,spaceBefore=5,spaceAfter=11),
 'EqSmall':dict(fontName='Serif',fontSize=9.8,leading=15.5,alignment=TA_CENTER,spaceBefore=5,spaceAfter=10),
 'CodeR':dict(fontName='Mono',fontSize=8.1,leading=11.5,spaceBefore=5,spaceAfter=10),
 'Cell':dict(fontName='Sans',fontSize=8.6,leading=11.7),
 'CellHead':dict(fontName='SansBold',fontSize=8.6,leading=11.7),
}.items():
    styles.add(ParagraphStyle(name=name,textColor=colors.black,**opts))
W,H=A4; M=52; story=[]
def p(s,sty='BodyR'): story.append(Paragraph(s,styles[sty]))
def h(s): p(s,'H')
def h2(s): p(s,'H2')
def eq(s,small=False): p(s,'EqSmall' if small else 'Equation')
def page(): story.append(PageBreak())
def code(s): story.append(Preformatted(s,styles['CodeR']))
def table(rows,widths,compact=False):
    cooked=[[Paragraph(str(c),styles['CellHead'] if i==0 else styles['Cell']) for c in row] for i,row in enumerate(rows)]
    t=Table(cooked,colWidths=widths,hAlign='CENTER',repeatRows=1)
    pad=4.5 if compact else 6
    cmds=[('VALIGN',(0,0),(-1,-1),'MIDDLE'),('LEFTPADDING',(0,0),(-1,-1),7),('RIGHTPADDING',(0,0),(-1,-1),7),('TOPPADDING',(0,0),(-1,-1),pad),('BOTTOMPADDING',(0,0),(-1,-1),pad),('BACKGROUND',(0,0),(-1,0),colors.HexColor('#eeeeee')),('LINEBELOW',(0,0),(-1,0),.7,colors.black),('LINEBELOW',(0,-1),(-1,-1),.5,colors.HexColor('#999999'))]
    for i in range(1,len(rows)):
        if i%2==0:cmds.append(('BACKGROUND',(0,i),(-1,i),colors.HexColor('#f8f8f8')))
    t.setStyle(TableStyle(cmds));story.append(t);story.append(Spacer(1,10))

# 1: uniform result and concrete instance
p('GPT-6 Astra','Label')
p('Extremal quadratic maps<br/>in dimensions divisible<br/>by four','TitleR')
p('A uniform existence theorem and a concrete twelve bit instance','Deck')
p('Research note and reproducible proof package · 9 October 2026','SmallR')
if not STATUS['verified']:
    p('<b>Working draft.</b> The uniform Lean theorem has compiled; independent source-only replay and the final certificate audit are still pending. This draft does not mark the formal package complete.','BodyR')
else:
    p('<b>Verified scope.</b> '+escape(STATUS['scope']),'BodyR')
h('The uniform theorem')
p('<b>Theorem.</b> For every integer e≥1 and n=4e, there exists a homogeneous quadratic map F:F<sub>2</sub><super>n</super>→F<sub>2</sub><super>n</super> of degree exactly two with')
eq('|N<sub>F</sub>| = 3 · 2<super>n/2−1</super> − 1.')
p('Here N<sub>F</sub> is the set of nonzero masks whose Boolean component is not bent. With the cited inequality [1], this attains Deryck’s non-MNBC lower bound for every m=n divisible by four. It does not settle dimensions congruent to two modulo four. The universal lower bound itself is cited, not part of the formal development.')
h('The explicit twelve bit instance')
p('A concrete map with eight independent quadratic coordinates and four zero coordinates has 4000 bent and 95 nonbent nonzero masks. In little-endian binary encoding its full nonbent set is')
eq('N<sub>F</sub> = {b ∈ {1,…,4095} : b mod 256 ∈ S},<br/>S = {0, 4, 8, 13, 14, 15}.')
p('The uniform proof makes classical choices of fields and coordinates. The explicit twelve-bit polynomial has a separate checked certificate; no byte-for-byte identification with the uniformly chosen e=3 witness is asserted. Sections 1 through 5 explain the concrete construction, and Appendix B proves the family.')
h('Novelty and attribution')
p('The underlying family is an established Jha–Johnson cyclic-semifield core plus a hyperbolic plane, identified by an explicit congruence. The exact extremal count is a short corollary; no prior publication of that consequence was located. Novelty is unestablished, and any contribution is at most a potentially new application or corollary. Appendix E gives the correspondence and sources.','SmallR')
p('“GPT-6 Astra” is the requested project label, not runtime model attribution.','SmallR')

# 2: explicit construction
page();h('1  The explicit construction')
p('Let k = F<sub>2</sub>[α]/(α<super>3</super>+α+1). The cubic has no root in F<sub>2</sub>, hence is irreducible. Thus k is a field with eight elements, with binary basis (1,α,α<super>2</super>). In particular α<super>3</super> = α+1 and α<super>4</super> = α<super>2</super>+α. Its trace is')
eq('Tr(c) = c + c<super>2</super> + c<super>4</super> ∈ F<sub>2</sub>.')
p('For λ = (u,v,w,z,s,t,p,q) ∈ F<sub>2</sub><super>8</super>, define a symmetric matrix K<sub>λ</sub> over k with zero diagonal and these six upper-triangular entries:')
eq('K<sub>01</sub> = u+v+α(s+t),<br/>K<sub>02</sub> = u+αs+α<super>2</super>q,<br/>K<sub>03</sub> = w+α<super>2</super>(p+q),<br/>K<sub>12</sub> = z+α<super>2</super>p,<br/>K<sub>13</sub> = v+αs+α<super>2</super>q,<br/>K<sub>23</sub> = u+v+αt.')
p('All eight parameters are binary, including when the expressions are evaluated in k. The parameter label is u+2v+4w+8z+16s+32t+64p+128q. The diagonal-zero symmetric matrix represents an alternating bilinear form in characteristic two.')
p('Write an input x ∈ F<sub>2</sub><super>12</super> as (X<sub>0</sub>,X<sub>1</sub>,X<sub>2</sub>,X<sub>3</sub>) ∈ k<super>4</super>, where')
eq('X<sub>i</sub> = x<sub>3i</sub> + αx<sub>3i+1</sub> + α<super>2</super>x<sub>3i+2</sub>.')
p('Let e<sub>j</sub> denote the jth binary parameter unit vector, with j beginning at zero. Define')
eq('F<sub>j</sub>(x) = Tr(Σ<sub>0≤i&lt;l≤3</sub> (K<sub>eⱼ</sub>)<sub>il</sub> X<sub>i</sub>X<sub>l</sub>)  (0 ≤ j &lt; 8),<br/>F<sub>8</sub> = F<sub>9</sub> = F<sub>10</sub> = F<sub>11</sub> = 0.',True)
p('This is an explicit homogeneous quadratic map in the twelve binary variables: multiplication in k is binary bilinear, and trace is binary linear. Appendix A gives all 66 vector coefficients, eliminating any need to implement field arithmetic to evaluate F.')
h2('The eight effective coordinates are independent')
p('The map λ ↦ K<sub>λ</sub> is injective. If K<sub>λ</sub> = 0, the basis coefficients in K<sub>02</sub> force u=s=q=0; K<sub>13</sub> then gives v=0; K<sub>12</sub> gives z=p=0; K<sub>03</sub> gives w=0; and K<sub>23</sub> gives t=0. Section 3 shows that trace also preserves this injectivity. Therefore the component kernel consists exactly of the four padded output-mask directions.')

# 3: Pfaffian
page();h('2  The Pfaffian calculation')
p('For an alternating four by four matrix over a field of characteristic two, set')
eq('pf(K) = K<sub>01</sub>K<sub>23</sub> + K<sub>02</sub>K<sub>13</sub> + K<sub>03</sub>K<sub>12</sub>.')
p('Expanding the determinant gives det(K) = pf(K)<super>2</super>: the three permutations consisting of two transpositions yield the three squared products, while the remaining nonzero determinant terms cancel in pairs. Hence K is singular exactly when pf(K)=0.')
h2('An explicit expansion')
p('Put A=u+v. Use a<super>2</super>=a for each binary parameter and α<super>4</super>=α<super>2</super>+α. The three products are')
eq('K<sub>01</sub>K<sub>23</sub> = A + αAs + α<super>2</super>(st+t),<br/>K<sub>02</sub>K<sub>13</sub> = uv + αAs + α<super>2</super>(qA+s) + (α<super>2</super>+α)q,<br/>K<sub>03</sub>K<sub>12</sub> = wz + α<super>2</super>(wp+z(p+q)) + (α<super>2</super>+α)(p+pq).',True)
p('Adding the products cancels the αAs terms and gives')
eq('pf(K<sub>λ</sub>) = P + αR + α<super>2</super>(Q+R),<br/>P = u+v+uv+wz,<br/>R = p+q+pq,<br/>Q = st+s+t+q(u+v)+wp+z(p+q).')
h2('Exactly six singular parameter values')
p('Linear independence of 1,α,α<super>2</super> makes pf(K<sub>λ</sub>)=0 equivalent to P=Q=R=0. For binary p,q, the expression p+q+pq is zero only when p=q=0. With these values fixed, Q=st+s+t is zero only when s=t=0. It remains to solve P=0.')
p('The expression u+v+uv is zero at (u,v)=(0,0) and one at the other three pairs. There are therefore three solutions with u=v=0 and wz=0, and three with (u,v)≠(0,0) and w=z=1. Their labels are exactly')
eq('S = {0, 4, 8, 13, 14, 15}.')
p('An alternating form has even rank. For completeness, if its value on a pair of vectors is nonzero, rescale the pair to obtain a nonsingular alternating two-dimensional block. Subtract multiples of that pair from each remaining basis vector to split off an orthogonal complement, and continue. Thus every nonzero singular four-dimensional alternating form has rank two.')
p('Injectivity from Section 1 makes label zero the only zero matrix. Consequently, among the 256 matrices K<sub>λ</sub>, one has rank zero, five have rank two, and 250 have rank four. This classification uses no numerical search.')

# 4: trace rank
page();h('3  Trace descent and binary rank')
h2('Nondegeneracy of the trace pairing')
p('The trace is binary linear since squaring is additive in characteristic two. Also Tr(c)<super>2</super>=Tr(c), using c<super>8</super>=c; the only roots of T<super>2</super>+T are zero and one, so its values lie in F<sub>2</sub>. Finally Tr(1)=1+1+1=1.')
p('If c≠0, choose d=c<super>−1</super>. Then Tr(cd)=Tr(1)=1. Thus the pairing (c,d) ↦ Tr(cd) is nondegenerate over F<sub>2</sub>. On k<super>4</super>, the coordinatewise pairing has the same property: isolate any nonzero coordinate and choose its inverse in the other vector.')
h2('The radical is unchanged as a set')
p('Associate to K<sub>λ</sub> the binary bilinear form')
eq('B<sub>λ</sub>(X,Y) = Tr(X<super>T</super>K<sub>λ</sub>Y).')
p('If K<sub>λ</sub>Y=0, then B<sub>λ</sub>(X,Y)=0 for every X. Conversely, if K<sub>λ</sub>Y has a nonzero coordinate c, choose X supported at that coordinate with value c<super>−1</super>. Then B<sub>λ</sub>(X,Y)=1, contradicting radical membership. Therefore')
eq('rad<sub>F₂</sub>(B<sub>λ</sub>) = ker<sub>k</sub>(K<sub>λ</sub>)<br/>as subsets of k<super>4</super>.')
p('A k-vector space of dimension d has binary dimension 3d. If K<sub>λ</sub> has k-rank r, the binary radical has dimension 3(4−r), and hence')
eq('rank<sub>F₂</sub>(B<sub>λ</sub>) = 12 − 3(4−r) = 3r.')
p('This proves the binary rank distribution without relying on an elimination program:')
table([['Binary rank','Number of effective masks','Effective labels'],['0','1','0'],['6','5','4, 8, 13, 14, 15'],['12','250','All remaining labels']], [90,170,215])
h2('The component polar form')
p('For b∈F<sub>2</sub><super>12</super>, write λ=(b<sub>0</sub>,…,b<sub>7</sub>) and f<sub>b</sub>(x)=⟨b,F(x)⟩. Linearity of trace and of K in λ gives')
eq('f<sub>b</sub>(X) = Tr(Σ<sub>i&lt;l</sub> (K<sub>λ</sub>)<sub>il</sub>X<sub>i</sub>X<sub>l</sub>),<br/>f<sub>b</sub>(X+Y)+f<sub>b</sub>(X)+f<sub>b</sub>(Y) = B<sub>λ</sub>(X,Y).',True)
p('In the ordered binary basis, its polar matrix M<sub>λ</sub> has entries M<sub>λ</sub>[3i+r,3l+h]=Tr(α<super>r+h</super>(K<sub>λ</sub>)<sub>il</sub>). Nondegeneracy also shows B<sub>λ</sub>=0 only when K<sub>λ</sub>=0. Therefore no nonzero effective mask selects the zero quadratic function.')

# 5: quadratic bent criterion
page();h('4  A self contained Walsh argument')
p('Let V=F<sub>2</sub><super>n</super> and let q:V→F<sub>2</sub> be quadratic with q(0)=0. Its polar form B(x,z)=q(x+z)+q(x)+q(z) is alternating bilinear. Write R for its radical and r=n−dim R for its rank. For a frequency a∈V, define')
eq('W<sub>q</sub>(a) = Σ<sub>x∈V</sub> (−1)<super>q(x)+⟨a,x⟩</super>.')
h2('The square of a Walsh coefficient')
p('In the product of two Walsh sums, replace the second variable by x+z. Bilinearity and character cancellation yield')
eq('W<sub>q</sub>(a)<super>2</super><br/>= Σ<sub>z∈V</sub> (−1)<super>q(z)+⟨a,z⟩</super> Σ<sub>x∈V</sub> (−1)<super>B(x,z)</super><br/>= 2<super>n</super> Σ<sub>z∈R</sub> (−1)<super>q(z)+⟨a,z⟩</super>.')
p('Indeed, the inner sum equals 2<super>n</super> for z∈R. Otherwise x↦B(x,z) is a nonzero linear functional; translation by a vector where it equals one pairs opposite signs and makes the sum zero.')
p('The restriction q|<sub>R</sub> is linear because B vanishes on R. The remaining character sum is |R| when ⟨a,·⟩ agrees with q on R, and zero otherwise. Every linear functional on R extends to V. There are exactly 2<super>n−dim R</super>=2<super>r</super> such extensions, since the annihilator of R has that size. Consequently')
eq('W<sub>q</sub>(a) ∈ {0, ±2<super>n−r/2</super>},<br/>#{a : W<sub>q</sub>(a)≠0} = 2<super>r</super>.')
p('If r=n, every coefficient has magnitude 2<super>n/2</super>, so q is bent. If r&lt;n, some coefficient has larger magnitude and q is not bent. Thus a quadratic Boolean function is bent exactly when its polar form is nonsingular.')
h2('The signs in the spectrum')
p('Summing W<sub>q</sub>(a) over a cancels every x≠0 and leaves 2<super>n</super>(−1)<super>q(0)</super>=2<super>n</super>. If A=2<super>n−r/2</super> and N<sub>+</sub>,N<sub>−</sub> count coefficients +A,−A, then')
eq('N<sub>+</sub>+N<sub>−</sub>=2<super>r</super>,<br/>A(N<sub>+</sub>−N<sub>−</sub>)=2<super>n</super>.')
p('For r&gt;0 this gives N<sub>±</sub>=2<super>r−1</super>±2<super>r/2−1</super>. There are 2<super>n</super>−2<super>r</super> zeros. The zero function has one coefficient 2<super>n</super>, at frequency zero, and all other coefficients zero. These identities prove every numerical spectrum in the next section.')

# 6: count + interpretation
page();h('5  Exact counts and sharpness')
p('Apply Sections 3 and 4 with n=12. Each effective mask selects a quadratic component of binary polar rank zero, six or twelve. The full spectrum of each component is as follows. Multiplicities in the last column count the 4096 input frequencies.')
table([['Effective mask','Count','Rank','Walsh values with multiplicities'],['0','1','0','0: 4095; 4096: 1'],['4, 8, 13, 14, 15','5','6','−512: 28; 0: 4032; 512: 36'],['All others','250','12','−64: 2016; 64: 2080']], [130,50,50,245])
p('The four zero output coordinates make each effective mask occur for 16 full masks. Thus 250·16=4000 nonzero masks are bent. The six singular effective masks have 6·16=96 preimages, one of which is the zero mask. Excluding that mask gives exactly 95 nonzero nonbent masks.')
eq('4095 = 4000 + 80 + 15.')
p('Here the 80 masks are 16 copies of each of the five rank-six components. The other 15 are nonzero masks supported entirely in the four padded positions, and they select the identically zero component. A nonzero mask selecting the zero function still belongs to N<sub>F</sub>.')
h2('The known lower bound applies')
p('MNBC denotes attaining the maximum number of bent components, equivalently |N<sub>F</sub>|=2<super>m−n/2</super>−1. For n=m=12 this is 63, so the witness is non-MNBC. Deryck [1, Theorem 5.4.15, printed p. 87] proves that a non-MNBC quadratic map satisfies')
eq('|N<sub>F</sub>| ≥ 2<super>m−n/2</super> + 2<super>m−n/2−1</super> − 1<br/>when n is even and n ≤ 2m−4.')
p('At n=m=12 the hypotheses hold and the right-hand side is 64+32−1=95. Together with the explicit witness, this establishes sharpness at that parameter pair. The universal inequality is cited; it is not re-proved or formalized in this package.')
# A mathematical corollary, deliberately distinct from the certified map.
page();h('6  A variant with independent output coordinates')
p('<b>Separate mathematical corollary.</b> The canonical map used for the finite certificate retains its four zero coordinates. A simple variant has twelve linearly independent coordinate functions and the same 4000/95 component count. This corollary is not claimed to be included in the Lean certificate.')
h2('Add four independent linear coordinates')
p('Keep the first eight quadratic functions and define')
eq('G(x) = (F<sub>0</sub>(x),…,F<sub>7</sub>(x),x<sub>0</sub>,x<sub>1</sub>,x<sub>2</sub>,x<sub>3</sub>).')
p('Write a mask as b=(λ,ρ), where λ∈F<sub>2</sub><super>8</super> and ρ∈F<sub>2</sub><super>4</super>. Let L(x)=(x<sub>0</sub>,x<sub>1</sub>,x<sub>2</sub>,x<sub>3</sub>). The selected component becomes')
eq('g<sub>b</sub>(x) = f<sub>b</sub>(x)+⟨ρ,L(x)⟩,<br/>W<sub>G</sub>(b,a)=W<sub>F</sub>(b,a+L<super>T</super>ρ).')
p('Thus the new Walsh spectrum is only a permutation of the old frequency list. Bentness and every signed spectrum are unchanged for each mask. In particular |N<sub>G</sub>|=95 and G has 4000 bent nonzero components.')
h2('No nonzero mask selects the zero function')
p('If λ≠0, the polar form of g<sub>b</sub> is the nonzero form B<sub>λ</sub>, since adding a linear function does not change polarization. Hence g<sub>b</sub> cannot be identically zero. If λ=0 and ρ≠0, the component is a nonzero combination of the four independent input coordinate functions. This proves linear independence of all twelve coordinate functions of G.')
p('The 15 nonzero masks in the former padded directions now select nonzero linear components. Such a component still has a single Walsh coefficient +4096 and 4095 zeros, with the nonzero coefficient moved away from frequency zero. It remains nonbent.')
h2('What the variant does and does not establish')
p('The quadratic parts still span an eight-dimensional space, and their polar ranks remain exactly the same. Moreover, adding a linear map changes each derivative by a constant output vector. It therefore preserves derivative fiber sizes and cannot turn this construction into an APN map.')
p('For the canonical F, each derivative x↦F(x+a)+F(x) lands in a 256-element output subspace. Its 4096 inputs force a fiber of size at least 16. For G, the last four derivative coordinates are fixed by a, and the same obstruction remains. Neither variant is presented as a deployment-ready cryptographic primitive.')
p('The bound in [1] does not require independent coordinate functions. This corollary nevertheless shows that the same numerical extremum can be realized without identically zero nonzero-mask components. The finite formalization targets F; the corollary for G is established by the argument above.','SmallR')

# 7: appendix explicit66
page();h('Appendix A  All binary coefficients')
p('For x∈F<sub>2</sub><super>12</super>, the encoded output is F(x)=⊕<sub>i&lt;j, xᵢxⱼ=1</sub> c<sub>ij</sub>. The decimal integer c<sub>ij</sub> is an eight-bit vector, with bit k the coefficient of x<sub>i</sub>x<sub>j</sub> in F<sub>k</sub>. Its top four output bits are zero. Pairs are listed lexicographically, reading down each of the three blocks.')
p('Each coefficient can also be recovered from the field formula: (c<sub>ij</sub>)<sub>k</sub> is the corresponding upper-triangular entry of the binary polar matrix M<sub>eₖ</sub>. Within a single three-bit input block the coefficients are zero.','SmallR')
pairs=list(combinations(range(12),2)); coeff=CERT['coordinate_masks_lex_pairs']
rows=[['Pair (i,j)','c<sub>ij</sub>','Pair (i,j)','c<sub>ij</sub>','Pair (i,j)','c<sub>ij</sub>']]
for r in range(22):
    row=[]
    for k in range(3):
        idx=22*k+r; i,j=pairs[idx]
        row += [f'({i}, {j})',str(coeff[idx])]
    rows.append(row)
table(rows,[91,66,91,66,91,66],compact=True)
p('The complete output truth table uses input integer Σ<sub>i=0</sub><super>11</super> 2<super>i</super>x<sub>i</sub>. Its SHA-256 below is computed over the 4096 output bytes in that input order, not over the JSON representation.','SmallR')
code('ae7383fd45347cbcf32eefec5a6750434967\ndd727fe6751a388f3ba6ff72bce3')

# General family appendix; independent from finite Lean certification.
page();h('Appendix B  A family in dimensions divisible by four')
if STATUS.get('uniform_verified'):
    p('<b>Uniform theorem.</b> The construction works for every e≥1 and n=4e. The mathematical proof below accompanies a checked Lean existence theorem; Appendix C identifies its exact scope and classical coordinate choices. Novelty remains provisional.')
else:
    p('<b>Uniform mathematical construction.</b> The proof below works for every e≥1 and n=4e. A corresponding Lean existence theorem has compiled, but independent source-only replay is pending. Novelty remains provisional.')
h2('Two anisotropic binary planes')
p('Identify the six-dimensional binary space Q=Alt(4,F<sub>2</sub>) with the upper-entry vectors (a,b,c,d,f,g) in pair order 01,02,03,12,13,23. Its Pfaffian quadratic form and polar pairing are')
eq('q(a,b,c,d,f,g)=ag+bf+cd,<br/>β(X,Y)=q(X+Y)+q(X)+q(Y).')
p('Define the four-dimensional space V and two binary planes O,H by')
eq('A(u,v,w,z)=(u+v,u,w,z,v,u+v),<br/>V={A(u,v,w,z)},<br/>O=span{(1,1,0,0,1,0), (1,0,0,0,0,1)},<br/>H=span{(0,0,1,1,0,0), (0,1,1,0,1,0)}.',True)
p('In either ordered basis of O or H, q(s·v<sub>1</sub>+t·v<sub>2</sub>)=s+t+st. Thus q equals one on each plane’s three nonzero vectors. Direct substitution gives β(V,O)=0 and β(H,O)=0. Also q(A)=u+v+uv+wz has the six zeros already counted in Section 2.')
h2('The extension pencil')
p('Let E=F<sub>2<super>e</super></sub> and choose α of degree e, so that 1,α,…,α<super>e−1</super> is a binary basis. For e=1 only 1 is used. Take X<sub>0</sub>=A∈V; for 1≤j&lt;e choose X<sub>j</sub>∈O when j is odd and X<sub>j</sub>∈H when j is even. Set')
eq('K = Σ<sub>j=0</sub><super>e−1</super> α<super>j</super>X<sub>j</sub> ∈ Alt(4,E).')
p('Coefficientwise independence makes this a binary pencil of dimension 4+2(e−1)=2e+2. Extending q and β to E gives')
eq('q(K) = Σ<sub>j</sub> α<super>2j</super>q(X<sub>j</sub>)<br/>+ Σ<sub>i&lt;j</sub> α<super>i+j</super>β(X<sub>i</sub>,X<sub>j</sub>).')
p('Every cross term with i+j odd vanishes: its two entries lie in O and either V or H. For an even sum, write i+j=2k; then i&lt;k&lt;j. Thus its basis index k is strictly below its larger active index j.')
p('Suppose m≥1 is the largest index with X<sub>m</sub>≠0. In the basis 1,α<super>2</super>,…,α<super>2(e−1)</super>, the coefficient at index m equals q(X<sub>m</sub>)=1; no cross term reaches it. These squared powers are independent because a relation between them is the square of the corresponding relation between 1,α,…,α<super>e−1</super>, and Frobenius is injective. Therefore q(K)≠0.')
p('Conversely, if all X<sub>j</sub>=0 for j≥1, then q(K)=q(A). Hence the entire pencil has exactly six singular matrices, regardless of e.')

page();h('Appendix B  Trace and the general count')
h2('Trace nondegeneracy in every extension degree')
p('For E=F<sub>2<super>e</super></sub>, write T(z)=z+z<super>2</super>+…+z<super>2<super>e−1</super></super>. Its values are binary because T(z)<super>2</super>=T(z). As a polynomial, T is nonzero and has degree 2<super>e−1</super>&lt;2<super>e</super>. A nonzero polynomial over a field has at most its degree many roots, so T is not identically zero on E. Therefore some z∈E satisfies T(z)=1.')
p('Given c≠0, take d=z/c. Then T(cd)=1, proving the trace pairing is nondegenerate. This argument is necessary for even e, when T(1)=0 and the shortcut used specifically for F<sub>8</sub> would fail.')
p('Exactly as in Section 3, the radical of the binary form (x,y)↦T(x<super>T</super>Ky) is the E-kernel of K viewed over F<sub>2</sub>. Thus its binary rank equals e times the E-rank. The pencil therefore has one form of rank zero, five of rank 2e, and 2<super>2e+2</super>−6 of rank 4e. Trace preserves the pencil’s binary dimension 2e+2.')
h2('The associated quadratic map')
p('Choose the induced binary basis of E<super>4</super>. For the 2e+2 basis matrices M<sub>k</sub> of the trace pencil, take coordinate functions f<sub>k</sub>(x)=Σ<sub>a&lt;b</sub>(M<sub>k</sub>)<sub>ab</sub>x<sub>a</sub>x<sub>b</sub>. Append 2e−2 zero coordinates. This gives F:F<sub>2</sub><super>4e</super>→F<sub>2</sub><super>4e</super>, with exactly six nonbent effective masks, including zero.')
eq('|N<sub>F</sub>| = 6 · 2<super>2e−2</super> − 1<br/>= 3 · 2<super>2e−1</super> − 1 = 3 · 2<super>n/2−1</super> − 1.')
p('The proof of the bent criterion in Section 4 applies unchanged. The resulting count is larger than the MNBC count 2<super>2e</super>−1. The cited general lower bound [1] applies for every e≥1, so this is equality for every positive input dimension divisible by four. No assertion about n≡2 mod 4 follows.')
h2('Finite cross checks')
p('The included family/verify_family.py checks every parameter over explicit fields for e=1,…,6. It validates each field by inverses, and finds exactly the same six singular labels in each case. These finite checks illustrate the proof; they do not replace its argument for all e.')
table([['e','Input bits n','Effective parameters','Nonzero nonbent masks'],['1','4','16','5'],['2','8','64','23'],['3','12','256','95'],['4','16','1024','383'],['5','20','4096','1535'],['6','24','16384','6143']], [50,90,155,180],compact=True)
p('At e=3, use α<super>3</super>+α+1=0 and the displayed O and H bases. Then K=A+αX<sub>1</sub>+α<super>2</super>X<sub>2</sub> is exactly the twelve-bit pencil of Section 1. The e=1 and e=2 counts already have prior constructions; this appendix does not claim them as newly discovered.','SmallR')

# 8: audit
page();h('Appendix C  Verification and trust boundary')
h2('Human mathematical proof')
p('Sections 1 through 5 and Appendix B give the algebraic proofs, including trace nondegeneracy and the Walsh criterion. Section 6 gives the linear-coordinate variant. These arguments can be checked without accepting generated certificates or Python results.')
h2('Exhaustive executable checks')
p('The dependency-free script verify_all.py regenerated the 66 binary coefficients from the six field formulas and checked all 256 field and binary ranks. It verified injectivity and the Pfaffian identity at every parameter. It also compared the binary and trace formulas at all 4096 inputs.')
p('For each of the 256 effective masks, it computed all 4096 Walsh coefficients using exact-integer fast Walsh transforms: 1,048,576 coefficients in total. It checked every full signed spectrum and separately recomputed 1536 raw Walsh sums, at six frequencies per mask. The spectra and truth table agree with a separately implemented NumPy computation supplied in independent/.')
p('These scripts are reproducibility checks. A correct execution depends on the interpreter, implementation and assertions; it is not by itself a proof-assistant certificate.')
h2('The explicit twelve bit Lean certificate')
if STATUS['verified']:
    for para in STATUS.get('report_paragraphs',[STATUS['scope']]): p(escape(para))
    if STATUS.get('theorems'): code('\n'.join(STATUS['theorems']))
else:
    p('<b>Pending.</b> The full twelve-bit theorem is not yet certified in Lean. Generic fast-Walsh equivalence and a quadratic component-expansion bridge have been proved in a separate Lean 4.19.0 development, and one actual twelve-bit component has been kernel-checked. The remaining components and final count are still pending. Neither a successful pilot nor the Python checks may be described as a completed 95-count theorem.')
    p('This working draft deliberately contains no statement that Lean has certified all 256 effective components, all 4095 nonzero masks, the full count, or the cited universal bound. A finalized package must identify the precise checked statements, build command, axiom output and reproducible source before making such a claim.')
page();h('Appendix C  The uniform formal theorem')
if STATUS.get('uniform_verified'):
    for para in STATUS.get('uniform_report_paragraphs',[]): p(escape(para))
    if STATUS.get('uniform_theorems'): code('\n'.join(STATUS['uniform_theorems']))
else:
    p('<b>Independent replay pending.</b> The theorem FamilyAlgebra.uniform_nonaffine_quadratic has compiled for arbitrary e&gt;0. Its statement asserts an actual BitVec(4e) map with a valid squarefree homogeneous quadratic representation, explicit nonaffineness, and exactly 3·2^(2e−1)−1 nonzero masks failing the original actual-Walsh bentness predicate. The final package will not mark this theorem independently verified until its frozen source-only replay succeeds.')
    p('The proof assembles finite-field existence, power-basis independence, the six-exception Pfaffian locus, trace nondegeneracy, binary coordinate transport, an upper-triangular quadratic constructor, the actual Walsh bent criterion and the exact mask count. It does not assume these links as unproved bridges.')
    p('The construction uses classical finite-dimensional choices of fields, bases and coordinate equivalences. It proves existence for each e; it is not an efficient coefficient-extraction algorithm for arbitrary e. Its specialization at e=3 is not identified byte-for-byte with the explicit 66-coefficient map.')
h2('Independent boundaries')
p('Formal verification cannot prove that a construction is historically new. Conversely, a novelty search cannot certify the mathematics. The cited general lower bound is an external mathematical dependency for the word “extremal,” separate from both the concrete and uniform existence/count theorems. The optional linear-coordinate corollary and the exact signed spectral multiplicities are proved mathematically in this note; they are not separate exported Lean claims.')
p('The requested project label “GPT-6 Astra” identifies this research deliverable. No claim about the underlying model runtime, human authorship, peer review, institutional endorsement or publication priority is made.')

# 9: reproducibility and citations
page();h('Appendix D  Reproducing and citing the result')
h2('Minimal finite check')
p('Use Python 3.10 or later. From the source directory, run:')
code('python3 verify_all.py')
p('No third-party package or network access is needed. The script fails on any inconsistent coefficient, rank, input value or Walsh spectrum; it writes results/reproduced.json. Expected final counts are 4000 bent and 95 nonbent nonzero masks. The supplied run log records a successful execution. For a separate NumPy implementation, consult independent/verify.py; its original relative paths are preserved as provenance, while verify_all.py is the portable entry point.')
p('To rebuild this PDF, install ReportLab in an isolated Python environment and run:')
code('python3 build_report.py')
p('Bundled fonts and requirements-pdf.txt record the rendering dependencies. Check SHA256SUMS before comparing files. The truth-table byte hash in Appendix A deliberately differs from the hash of its JSON file.')
if STATUS['verified']:
    h2('The two Lean projects')
    p(escape(STATUS.get('reproduction','See lean/README.md for the exact clean-build instructions.')))
    if STATUS.get('command'):
        p('Starting from the source directory:','SmallR')
        code(STATUS['command'])
    if STATUS.get('uniform_reproduction'): p(escape(STATUS['uniform_reproduction']))
    if STATUS.get('uniform_command'):
        p('Starting again from the source directory:','SmallR')
        code(STATUS['uniform_command'])
page();h('Appendix E  The established construction mechanism')
p('The pencil of Appendix B is explicitly congruent to a hyperbolic binary plane plus a Jha–Johnson cyclic-semifield core. Thus its underlying construction is established. The exact extremal component-count consequence was not located as a published statement; its novelty remains unestablished. The correspondence and elementary corollary are given here so this distinction is auditable.')
h2('An explicit change of basis')
p('Use the six-bit alternating-matrix encoding in Appendix B. Put D=span{47,61}; direct calculation gives V=D⊕H. The invertible binary matrix below acts by M↦P<super>T</super>MP:')
eq('P = [(1,1,1,0); (0,1,1,1);<br/>     (1,0,1,0); (0,1,0,1)].')
p('Its columns have masks 5,11,7,10. The images of the ordered bases are D:(47,61)↦(1,32), H:(12,22)↦(18,28), and O:(19,33)↦(22,26). The latter two pairs occupy the cross block between the first and last two coordinates. In that block they are (I,R) and (J,JR), where')
eq('R = [(0,1); (1,1)],   J = [(1,1); (0,1)],<br/>R<super>2</super>+R+I=0,   J<super>2</super>=I,   JR=R<super>2</super>J.')
p('Write K=span<sub>F₂</sub>{I,R}, a matrix field isomorphic to F<sub>4</sub>, with conjugation C↦C̄=C<super>2</super>. The transformed base parameters are x=u+w+z, y=v+w+z, h<sub>0</sub>=u+v+z, h<sub>1</sub>=w+z. This binary change is invertible. The full pencil consists of')
eq('M(x,y,B) = [(xZ,B); (B<super>T</super>,yZ)],<br/>Z=[(0,1);(1,0)],   x,y∈F<sub>2</sub>,<br/>B∈S=Σ<sub>0≤j&lt;e</sub> T<super>j</super>K,   T=αJ.',True)
p('Here B=h<sub>0</sub>I+h<sub>1</sub>R+Σ<sub>j=1</sub><super>e−1</super>α<super>j</super>J<super>j mod 2</super>(s<sub>j</sub>I+t<sub>j</sub>R). Thus this is equality of pencils after a fixed congruence, rather than a numerical resemblance.')
h2('Why this is a cyclic semifield core')
p('On E<super>2</super>, the matrix field K gives an e-dimensional K-vector space. T is semilinear for the nontrivial automorphism of K and T<super>2</super>=γI, with γ=α<super>2</super>. For e&gt;1, γ generates E over F<sub>2</sub>. The algebra generated by K and T contains E and J and hence all Mat<sub>2</sub>(E), since I,R,J,JR are E-linearly independent. No proper nonzero K-subspace can be T-invariant. For e=1, take α=γ=1; irreducibility is automatic in K-dimension one.')
p('This is precisely the irreducible-semilinear construction recalled by Kantor and Liebler [5, §2, p. 334]. Its odd-e norm and power-basis presentation is also given by Johnson, Marino, Polverino and Trombetti [6, Theorem 1(2), pp. 10–11]. The general argument above includes even e; [6] is cited only for its odd-e specialization.','SmallR')

page();h('Appendix E  The determinant fibre corollary')
p('The following elementary refinement counts the determinant-one fibre of the established core S. It explains how the six singular forms, and hence the extremal component count, follow from that mechanism. This correspondence is a mathematical identification; the frozen Lean proof uses Appendix B directly and does not depend on a new citation axiom.')
h2('A polynomial over the binary field')
p('Separate the even and odd powers in B. With γ=α<super>2</super>, write')
eq('B=h(γ)+T o(γ),<br/>h(X)=Σ<sub>2j&lt;e</sub>C<sub>2j</sub>X<super>j</super>,<br/>o(X)=Σ<sub>2j+1&lt;e</sub>C<sub>2j+1</sub>X<super>j</super>,   C<sub>j</sub>∈K.')
p('For a polynomial with coefficients in K, a bar means coefficientwise conjugation C↦C<super>2</super>; the variable X is fixed. Direct two by two determinant expansion, using JR=R<super>2</super>J, gives')
eq('det B = f(γ),<br/>f(X)=h(X)h̄(X)+X o(X)ō(X) ∈ F<sub>2</sub>[X].')
p('The two products are fixed by conjugation. If h is nonzero, its product with h̄ has degree 2 deg h, with leading coefficient one, since each nonzero element of K has norm one to F<sub>2</sub>. If o is nonzero, Xoō has odd degree 2 deg o+1, also with leading coefficient one. These leading degrees have different parity and cannot cancel. Both are at most e−1.')
p('Since γ has degree e, evaluation is injective on binary polynomials of degree less than e. Therefore det B=0 forces h=o=0. Likewise det B=1 forces o=0 and h a nonzero constant. Exactly three constants in K are nonzero, so')
eq('#{B∈S : det B=0}=1,<br/>#{B∈S : det B=1}=3.')
p('For e=1 the same assertion follows directly from S=K. For even e the expression hh̄+Xoō is a formal coefficientwise identity; it is not an assertion that E adjoined with K is a quadratic field extension. This avoids an invalid field-norm interpretation in that case.')
h2('Adjoin the two hyperbolic directions')
p('The block matrix from the previous page has Pfaffian xy+det B. If B=0, precisely the three pairs with xy=0 make it vanish. If det B=1, each of the three possible B has the single pair x=y=1. There are no other solutions because xy is binary. Thus there are exactly six singular matrices, including zero.')
eq('6·2<super>2e−2</super>−1 = 3·2<super>2e−1</super>−1.')
p('Trace descent, the quadratic bent criterion and output padding give the displayed count, as in Appendix B. The count is therefore a short determinant-fibre corollary of an established core. It should not be advertised as a new underlying family. The package includes family/CYCLIC_SEMIFIELD_CORRESPONDENCE.txt and a dependency-free checker for the congruence and finite determinant fibres.','SmallR')

page();h('Appendix E  Literature and sources')
p('Deryck’s printed p. 88 asks for higher-dimensional equality [1]. The mathematical and Lean results here attain the bound for equal dimensions divisible by four. The explicit correspondence above identifies the family mechanism with established cyclic-semifield machinery [5,6]. A targeted search located no prior publication of this exact extremal component-count consequence. That limited negative finding does not establish priority; specialist review remains necessary. Any potentially new contribution is the application or corollary and its formal verification, not the underlying construction.')
p('Trace descent and rank multiplication are established [2]. The broader geometric correspondence with additive semifield spread sets also appears in [4, Theorem 16]. Eight-bit numerical existence follows already from [3, Definition 4.1 and Table 4.1]: a final profile pair (58,78) or (58,90) gives a six-dimensional component space with 58 bent functions. Padding by two output zeros yields 232 bent and 23 nonbent nonzero masks. No equivalence of those examples to this formula is asserted.')
h2('References')
p('[1] Maxime Deryck. <i>Cryptography meets Finite Geometry.</i> Master’s thesis, Ghent University, academic year 2025–2026. Theorem 5.4.15, printed p. 87; higher-dimensional discussion, printed p. 88. <link href="https://maximederyck.be/assets/Cryptography%20meets%20Finite%20Geometry.pdf" color="#16426b">Author-hosted thesis PDF</link>.','SmallR')
p('[2] Rod Gow. <i>Rank-related dimension bounds for subspaces of bilinear forms over finite fields.</i> arXiv:1703.07266v1, 21 March 2017. See the proof of Theorem 6 for trace descent. <link href="https://arxiv.org/abs/1703.07266" color="#16426b">arXiv record</link>; <link href="https://arxiv.org/html/1703.07266" color="#16426b">full text</link>.','SmallR')
p('[3] Christof Beierle, Philippe Langevin, Gregor Leander, Alexandr Polujan and Shahram Rasoolzadeh. <i>Millions of inequivalent quadratic APN functions in eight variables.</i> arXiv:2508.04644v1, 6 August 2025. Definition 4.1 and Table 4.1. <link href="https://arxiv.org/html/2508.04644v1" color="#16426b">Full text</link>.','SmallR')
p('[4] Guglielmo Lunardon. <i>50 Years of translation structures.</i> Journal of Geometry 113, article 35 (2022). Section 3.3.3 and Theorem 16. DOI: 10.1007/s00022-022-00643-5. <link href="https://link.springer.com/article/10.1007/s00022-022-00643-5" color="#16426b">Publisher full text</link>.','SmallR')
p('[5] William M. Kantor and Robert A. Liebler. <i>Semifields arising from irreducible semilinear transformations.</i> Journal of the Australian Mathematical Society 85 (2008), 333–339. Section 2, printed p. 334. DOI: 10.1017/S1446788708000888. <link href="https://pages.uoregon.edu/kantor/PAPERS/IrreducibleSemilinear.pdf" color="#16426b">Author-hosted PDF</link>.','SmallR')
p('[6] Norman L. Johnson, Giuseppe Marino, Olga Polverino and Rocco Trombetti. <i>On a generalization of cyclic semifields.</i> Journal of Algebraic Combinatorics 29 (2009), 1–34. Theorem 1(2), pp. 10–11, for odd extension degree. DOI: 10.1007/s10801-007-0116-x. <link href="https://emis.de/ft/43764" color="#16426b">Full text PDF</link>.','SmallR')
p('External sources were checked on 9 October 2026. Only the general bound and historical context rely on these citations; the finite construction and its proof are explicit in this note.','SmallR')

OUT.parent.mkdir(parents=True,exist_ok=True)
def footer(canvas,doc):
    canvas.saveState();canvas.setFont('Sans',7.6);canvas.setFillColor(colors.HexColor('#666666'))
    suffix='Working draft' if not STATUS['verified'] else 'Research note'
    canvas.drawString(M,30,'GPT-6 Astra · Extremal quadratic family · '+suffix)
    canvas.drawRightString(W-M,30,str(doc.page))
    canvas.restoreState()
doc=SimpleDocTemplate(str(OUT),pagesize=A4,rightMargin=M,leftMargin=M,topMargin=44,bottomMargin=49,title='Extremal quadratic maps in dimensions divisible by four',author='GPT-6 Astra (project label)',subject='Uniform sharpness construction for dimensions divisible by four and explicit twelve-bit certificate')
doc.build(story,onFirstPage=footer,onLaterPages=footer)
print(OUT)
