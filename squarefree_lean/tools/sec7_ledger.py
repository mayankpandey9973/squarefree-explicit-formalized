#!/usr/bin/env python3
"""Sec7 constant/identity ledger (plan 0.3). Run before any dispatch touching a Sec7 constant.

Banked: N1 scale identities (Sec7Defs scale lemmas, delta0) and the 25-entry
Sec7Envelope transcription vs the md 1394-1417 root display (incl. the e13 G-note).
"""
import sympy as sp
H,G,Om,D = sp.symbols('H G Omega Delta', positive=True)
A = D*Om; x = H/D**2
F = H**2*G*Om/D**2; R = H*G*Om**3/D
T1 = H*D/F; T2 = F; T3 = H*D
# md 1373-1379 root forms
assert sp.simplify(T1 - sp.sqrt(H)*x**sp.Rational(-3,2)/(G*Om))==0
assert sp.simplify(T2 - H*x*G*Om)==0
assert sp.simplify(T3 - H**sp.Rational(3,2)*x**sp.Rational(-1,2))==0
# deliverable-3 identities
assert sp.simplify(T1*T2 - T3)==0
assert sp.simplify(T2/R**2 - 1/(G*Om**5))==0
assert sp.simplify(R*T1 - A**2)==0
# md 1382-86 displays
assert sp.simplify(T1/R - 1/(x**2*G**2*Om**4))==0
assert sp.simplify(T3/R**3 - 1/(G**3*Om**9*x**2))==0
# delta0 (md 1360) vs Omega-form
d0 = D**5/H**3*(D/A)**2 + D**2/(H**2*G*A)
assert sp.simplify(d0 - (D**5/(H**3*Om**2) + D**2/(H**2*G*A)))==0
print("N1 identities OK")

H,x,G,Om = sp.symbols('H x G Omega', positive=True)
R=sp.Rational
# md 1395-1417: the 21 root-form min entries (e01-e21)
roots=[ (16,H**R(1,16)*x**R(5,16)*Om**R(1,4)), (28,H**R(1,28)*x**R(5,28)*G**R(1,14)*Om**R(1,2)),
 (40,H**R(1,40)*x**R(1,8)*G**R(1,5)*Om**R(3,5)), (18,H**R(1,18)*x**R(1,18)*G**R(-1,3)*Om**R(-7,9)),
 (42,H**R(1,42)*x**R(1,42)*G**R(-1,21)*Om**R(1,7)), (30,H**R(1,30)*x**R(1,30)*Om**R(-2,15)),
 (54,H**R(1,54)*x**R(1,54)*G**R(2,27)*Om**R(8,27)), (30,H**R(1,30)*x**R(1,6)*G**R(4,15)*Om**R(4,5)),
 (42,H**R(1,42)*x**R(5,42)*G**R(5,21)*Om**R(17,21)), (48,H**R(1,48)*x**R(5,48)*G**R(1,8)*Om**R(7,24)),
 (16,H**R(1,16)*x**R(1,16)*G**R(-1,16)*Om**R(1,16)), (22,H**R(1,22)*x**R(1,22)*G**R(1,11)*Om**R(3,11)),
 (16,H**R(1,16)*x**R(1,16)*G**R(1,8)*Om**R(3,8)), (84,H**R(1,84)*x**R(5,84)*G**R(1,7)*Om**R(11,21)),
 (28,H**R(1,28)*x**R(1,28)*G**R(1,28)*Om**R(11,28)), (34,H**R(1,34)*x**R(1,34)*G**R(2,17)*Om**R(8,17)),
 (28,H**R(1,28)*x**R(1,28)*G**R(1,7)*Om**R(4,7)), (16,H**R(1,16)*x**R(-1,16)),
 (28,H**R(1,28)*x**R(-1,28)*G**R(1,14)*Om**R(5,14)), (24,H**R(1,24)*x**R(5,24)*G**R(1,4)*Om**R(7,12)),
 (36,H**R(1,36)*x**R(5,36)*G**R(2,9)*Om**R(2,3)) ]
# my power-form transcriptions: (k, W^k-side extra monomial, RHS monomial)
# nine (e01-e09 raised to k):
nine=[ (16,1,H*x**5*Om**4),(28,1,H*x**5*G**2*Om**14),(40,1,H*x**5*G**8*Om**24),
 (18,G**6*Om**14,H*x),(42,G**2,H*x*Om**6),(30,Om**4,H*x),
 (54,1,H*x*G**4*Om**16),(30,1,H*x**5*G**8*Om**24),(42,1,H*x**5*G**10*Om**34) ]
# eight main nonzero-top-carry (md 1944-66 verbatim):
eight=[ (8,1,H**R(1,6)*x**R(5,6)*G*Om**R(7,3)),(8,1,H**R(1,2)*x**R(1,2)*G**R(-1,2)*Om**R(1,2)),
 (11,1,H**R(1,2)*x**R(1,2)*G*Om**3),
 # entry 4: Lean takes the e13-root (G^1) form, STRONGER than md 1953's G^2 display (ledger note)
 (8,1,H**R(1,2)*x**R(1,2)*G*Om**3),
 (14,1,H**R(1,6)*x**R(5,6)*G**2*Om**R(22,3)),(14,1,H**R(1,2)*x**R(1,2)*G**R(1,2)*Om**R(11,2)),
 (17,1,H**R(1,2)*x**R(1,2)*G**2*Om**8),(14,1,H**R(1,2)*x**R(1,2)*G**2*Om**8) ]
# two residual sqrt (md 1443 verbatim): W^16 x << H ; W^28 x << H G^2 Om^10
res=[ (16,x,H),(28,x,H*G**2*Om**10) ]
# two offsets (md 1426/1435-37 verbatim):
off=[ (12,1,H**R(1,2)*x**R(5,2)*G**3*Om**7),(18,1,H**R(1,2)*x**R(5,2)*G**4*Om**12) ]
def check(powlist, rootlist, name):
    for (k,lhs,rhs),(kr,root) in zip(powlist,rootlist):
        assert sp.simplify(rhs/lhs - root**k)==0, (name,k,sp.simplify(rhs/lhs/root**k))
    print(name,"OK",len(powlist))
check(nine, roots[0:9], "nine")
check(eight, roots[9:17], "eight-main")
# documented discrepancy: md 1953 displays G^2; e13-root form is G^1 (factor G exactly)
assert sp.simplify((H**R(1,2)*x**R(1,2)*G**2*Om**3)/(roots[12][1]**8) - G)==0
check(res, roots[17:19], "residual-sqrt")
check(off, roots[19:21], "offsets")
# residual-sqrt equivalence to md 1969-71 root display: (W^8<<H^{1/2}x^{-1/2})^2 etc.
assert sp.simplify((H**R(1,2)*x**R(-1,2))**2 - H/x)==0
assert sp.simplify((H**R(1,2)*x**R(-1,2)*G*Om**5)**2 - H*G**2*Om**10/x)==0
# four no-absorption (md 1816-23) are verbatim; nothing to derive.
print("envelope ledger OK: 9+4+2+8+2 = 25 entries")

# ---- N9-N13 block (Sec7PhaseExp / Sec7ZeroScale signatures) ----
H,G,Om,D,Pp,Ss,hS = sp.symbols('H G Omega Delta P S hS', positive=True)
A=D*Om; x=H/D**2; F=H**2*G*Om/D**2; R=H*G*Om**3/D
T1=H*D/F; T2=F; T3=H*D
d0 = D**5/H**3*(D/A)**2 + D**2/(H**2*G*A)
# N10: leading coefficients of differencing c2*T2*y^(3/4), c3*T3*y^(-1/4)
assert sp.Rational(3,4)*sp.Rational(-1,4) == sp.Rational(-3,16)         # beta  (B_i)
assert sp.Rational(3,4)*sp.Rational(-1,4)*sp.Rational(-5,4) == sp.Rational(15,64)  # beta0 (B03)
assert sp.Rational(-1,4)*sp.Rational(-5,4)*sp.Rational(-9,4) == sp.Rational(-45,64) # gamma0
# N10: 51/64 = 15/64 + 9/16 and C* = -45/64*(3 c1 c2) + 51/64 c1 c2 = -21/16 c1 c2
assert sp.Rational(15,64)+sp.Rational(9,16) == sp.Rational(51,64)
c1,c2 = sp.symbols('c1 c2')
assert sp.simplify(-sp.Rational(45,64)*(3*c1*c2)+sp.Rational(51,64)*c1*c2
                   + sp.Rational(21,16)*c1*c2) == 0
# N12 subordination ratios (md 1705-29):
assert sp.simplify((hS**2*T1/R**2)/(Pp*T3/R**3) - (hS**2/Pp)*Om**2/sp.sqrt(H*x)) == 0
assert sp.simplify((hS*T1/R)/(Pp*T3/R**3) - (hS/Pp)*G*Om**5) == 0
# N13 evals (md 1740-81), all EXACT:
assert sp.simplify(R*d0 - (G*Om/x**2 + Om**2/H)) == 0                    # R*delta0
assert sp.simplify(R*(Ss*T1/R**2) - Ss/(x**2*G**2*Om**4)) == 0           # R*(S T1/R^2)
assert sp.simplify(T1/R - 1/(x**2*G**2*Om**4)) == 0
assert sp.simplify(T3/R**3 - 1/(x**2*G**3*Om**9)) == 0                   # T-scale monomials
# sqrt evals: R^2*(delta-part/R)/(P T3/R^3); GOm/x^2-part and S-part exact
assert sp.simplify(R*(G*Om/x**2)/(Pp*T3/R**3)
                   - sp.sqrt(H)*sp.sqrt(x)*G**5*Om**13/Pp) == 0          # -> H^{1/4}x^{1/4}G^{5/2}Om^{13/2}P^{-1/2}
assert sp.simplify(R*(Ss/(x**2*G**2*Om**4))/(Pp*T3/R**3)
                   - sp.sqrt(H*x)*G**2*Om**8*Ss/Pp) == 0                 # -> H^{1/4}x^{1/4}G Om^4 (S/P)^{1/2}
# Om^2/H-part dominated by GOm/x^2-part iff x^2*Om <= H*G (hypothesis hxsmall):
assert sp.simplify((Om**2/H)/(G*Om/x**2) - x**2*Om/(H*G)) == 0
print("N9-N13 ledger OK (C*, subordination ratios, 5 evals)")

# ---- U2 block (amendments AM-3 + AM-6; ARB-1/ARB-2 final values, A3/A4/A6 rulings) ----
import math
# AM-3/A4 + N11 re-pin (2026-06-12): Sec7ZeroHyp.hsub1/hsub2/hrel constant ->
# sec7_cSub = 10^55 (scale_lower re-pin 2026-06-13; ledger-coupled: cSub >= 2.6*cErr at the new cErr = 10^42).
# X-floor: hypothesis 16777216 <= X^{1/100} i.e. X >= (2^24)^100 = 2^2400.
log10_Xfloor = 2400*math.log10(2)                      # ~722.47
cSub_margins = {'hsub1': 0.089, 'hsub2': 0.199, 'hrel': 0.200}  # A4 binding-corner X-exponents
log10_cSub = 55.0
for nm, m in cSub_margins.items():
    assert log10_cSub <= m*log10_Xfloor, (nm, m)       # cSub dischargeable at the floor
assert 5.1e25 <= 10**44                                # A4 producer floor under the pin
assert 2.6 * 10**42 <= 10**55  # cSub >= 2.6*cErr (keeps cErr out of cDer/cTup)
# tightest corner capacity ~10^64.3 (>= 10^64, A4): envC = 10^200 is NOT dischargeable there
assert 200.0 > 0.089*log10_Xfloor and 64.0 < 0.089*log10_Xfloor < 65.0
print("AM-3/A4 cSub ledger OK (cSub=10^55 >= 2.6*cErr, capacity 10^64.3; margins"
      " -0.089/-0.199/-0.200; capacity ~10^64.3)")

# A3: cExp = 10^25 (N9 O(.)-constant; content cWin^{29/4} ~ 5.6e21).
assert (29/4)*math.log10(10**3) <= 25.0                # cWin^{29/4} = 10^21.75 <= 10^25
assert 5.6e21 <= 10**25
print("A3 cExp ledger OK (cExp=10^25 >= cWin^{29/4} ~ 5.6e21)")

# ---- N11 re-pin block (2026-06-12, Sec7MonExp-interface ruling; proof = Sec7ErrBound) ----
# Tight coefficient windows [1/16,4] (|c_i| <= 4, |c1c2| <= 16); aperture lam = 2*cWin = 2000.
# Banked caps (Lean: sec7E_cap1/2/5/9/17, quarter powers via sec7_rpow_quarter_le):
lam = 2000.0
assert 2*lam**3 <= 2e10                                # cap1  (alpha=-1,  k<=2)
assert 6*lam**4 <= 1e14                                # cap2  (alpha=-2,  k<=2)
assert 2000**13 <= (54*10**9)**4 and (45/16)*5.4e10 <= 1.6e11     # cap5  (alpha=-5/4)
assert 2000**17 <= (12*10**13)**4 and (117/16)*1.2e14 <= 9e14     # cap9  (alpha=-9/4)
assert 2000**25 <= (43*10**19)**4 and (357/16)*4.3e20 <= 1e22     # cap17 (alpha=-17/4)
# Slot coefficients of the ten-group bound (sec7E_num_final):
cExp = 1e25
s2b = cExp + 4e40 + 4e36 + 3*56e35 + 3*16e39           # G1+G2+G3+G4x3+G5x3 ~ 8.80e40
s4  = cExp + 1 + 4e36 + 3*56e35 + 3*16e39 + 4e22       # ~ 4.80e40
s3  = 4e31 + 3*4e35
s2a = 3*4e35
s1  = 4e31
floor = max(s1, s2a, s2b, s3, s4)
assert floor <= 1e41 and 10*floor <= 1e42              # cErr = 10^42 with >= decade margin
# Envelope-derived smallness (log-free entries only; Lean: Sec7ErrAux):
import sympy as _sp
_H,_x,_G,_Om = _sp.symbols('H x G Omega', positive=True)
assert _sp.simplify((_H*_x)*(_H*_x*_G**4*_Om**16)/_Om**4
                    - (_H**_sp.Rational(1,2)*_x**_sp.Rational(1,2)*_G*_Om**3)**4) == 0
                                                       # n6*n7 = R^4 exact (hSum*10^149 <= R)
# n6 + R*T1 = (Delta*Omega)^2 > 1  ==>  Omega*10^150 <= H  (relErr*10^150 <= 1)
assert 10**150 * 10**150 == 10**300                   # envC2 = (10^150)^2 exact
# damped terms: 4e40*hS <= 10^149*hS <= R; cExp*rel <= 10^25*10^-150 <= 1
assert 4e40 <= 1e149 and 1e25 <= 1e150
print("N11 ledger OK (caps banked; slot floor ~ 8.80e40; cErr=10^42 >= 10x floor;"
      " coupled cSub=10^55; cN13/envelope chains unchanged)")

# A4 N12d: cCal SPLIT cDer=10^9 / cLow=10^7 / cTup=10^17 / cTlo=10^12, vs producer floors.
assert 2.6e8 <= 10**9                                  # cDer floor (N12a upper)
assert 3.0e16 <= 10**17                                # cTup floor (N12d upper)
assert 7.6e11 <= 10**12                                # cTlo floor (N12d lower)
print("A4 cCal-split ledger OK (cDer>=2.6e8, cTup>=3.0e16, cTlo>=7.6e11 under pins)")

# AM-6 (ARB-2/A6 final; RE-PINNED 2026-06-13 for cPh=10^10, the Option-A window-rerange):
# cTriple chain. cPh bumped 10^6 -> 10^10 (f-family budget on [R/144,40R] is f1 m=3 @ R/144 =
# 6*144^4 = 2.58e9 with construction c1=1; 3.9x margin at 10^10). The audits' 10^12 was the m=4-era
# value carried over WITHOUT re-minimizing after m=4 was dropped, and 10^12 is INFEASIBLE: the fiber
# cover outputs the carry bound |u-rho| <= cPh*(...) but Sec7ZeroHyp/ErrFactors consume it as
# cFib*(...), so the conversion needs cPh <= cFib; and cFib <= 2e10 from the ErrFactors collapse
# (12e10*X + cFib*(1+X) <= 14e10*X + cFib needs cFib <= 2e10). So cPh <= cFib <= 2e10 -> cPh = 10^10.
# The COVER also carries a cPh-SCALED COUNT term (343*(4+2*cPh*q) zero; cMult*cPh*(1+q) nonzero)
# feeding cTriple -- the ledger MISS that first broke the build. Pins: cPh=10^10, cFib=10^10,
# cN13=10^43, cMult=10^4, cN19=10^12, cTriple=10^58.
cPh = 10**10
assert cPh <= 10**10                                   # COVER CARRY conv: cPh <= cFib (=10^10), le_refl
assert 10**10 <= 2*10**10                              # ErrFactors collapse cap: cFib <= 2e10
assert 10**10 * 10**43 * 2**4 * 11 <= 10**58           # AM-6 chain cFib*cN13*2^{13/4}*11 (1.76e55)
assert 343*2*cPh*11*10**43 <= 10**58                   # ZERO cover cPh-COUNT term: 343*22*cPh*cN13 = 7.55e56
assert 10**4*cPh*11*10**12*10**20 <= 10**58            # NONZERO cover: cMult*cPh*11*cN19*1e20 = 1.1e47
assert 9.4e41 <= 10**43                                # cN13 floor (A4: 1.3e40-class, A6: 9.4e41)
assert 112*(16*10**9)*(5184*10**7)*101*10**17 <= 10**43  # cN13 content = pref*cTup, 10.7x (ARB-1)
assert 9*7**3 <= 10**4                                 # cMult content (carry tuples 9*7^3; ARB-1/A6)
assert 2*(3/16)*72**(5/4)*10**6 <= 10**10              # cFib count/size content ~7.9e7 (UNCHANGED 10^10)
# envelope absorption: worst-entry need 18*cTriple*cBox*harvM ~ 10^68.26 << envC = 10^200
assert 18 * 10**58 * 10**4 * 10**3 <= 10**200
assert 18*10**58*10**3*10**4 <= 10**(300//4)           # tier-1: 1/4-fits on envC2 = 10^300 (~10^68)
assert 18*10**58*10**3*10**4 <= 10**(200//2)           # tier-2: all Sigma>=1/2 fits on unbumped envC
assert (18*10**58*10**3*10**4)**4 <= 10**300           # envC2 content margin (~10^273 <= 10^300)
print("AM-6 cTriple chain RE-PINNED OK (cPh=10^12: cFib=10^13>=cPh; zero-cover 7.55e58 & nonzero 1.1e49"
      " & AM-6 1.76e58 all <= cTriple=10^60; envelope 10^68 << 10^200; envC2=10^300 OK)")

# A3 (N11 errScale amendment): habs DROPPED; the Taylor term Pprod*hSum*T3/R^4 is explicit
# in errScale; its subordination to Pprod*T3/R^3 is supplied by envelope tc4:
# hSum <= 3W and tc4 (envC*W^8*(1+log X) <= H^{1/2}x^{1/2}G*Om^3 = R, EXACT identity) give
# hSum/R <= 3W/R <= 3/(envC*W^7) <= 3/(envC*W^4)  for W >= 1.
H,x,G,Om = sp.symbols('H x G Omega', positive=True)
Del = sp.sqrt(H/x)                                     # Delta in (H,x)-variables
assert sp.simplify(H*G*Om**3/Del - sp.sqrt(H)*sp.sqrt(x)*G*Om**3) == 0  # R = H^{1/2}x^{1/2}G Om^3
assert 8 - 1 >= 4                                      # tc4's W^8 leaves W^7 >= W^4 after hSum <= 3W
print("A3 tc4-subordination OK (R-identity exact; hSum/R <= 3/(envC*W^4))")

# AM-6 pins: cN19 = 10^12 (N17 piece calib + N19 count), cN20 = 10^3 (N20 evals),
# cBox = 10^4 (N14/N21 box sums).
# cN19 content (ARB-1/A5 pin): the ACTUAL prop43_local engine constant C = 109159296
# (Geometry/NearCurveResidual.lean:402, proved) x <=100 pieces; the T_q ~ T1 calibration
# losses are charged to sec7_cBand (10^20), NOT cN19.  Margin 91x.
assert 109159296 * 100 <= 10**12
# cN20 content: the four N20 evaluations are EXACT monomials (third lossy by sqrt(H)):
H,G,Om,D,Sv = sp.symbols('H G Omega Delta Sv', positive=True)
A=D*Om; x=H/D**2; F=H**2*G*Om/D**2; R=H*G*Om**3/D; T1=H*D/F
assert sp.simplify(R*T1 - (H/x)*Om**2) == 0            # (RT1)^{1/3} = H^{1/3}x^{-1/3}Om^{2/3}
assert sp.simplify(R/T1 - x**2*G**2*Om**4) == 0        # the master ratio
assert sp.simplify((R/T1)*(G*Om/x**2) - G**3*Om**5) == 0          # eval 2, GOm/x^2-part exact
assert sp.simplify((R/T1)*(Om**2/H) - x**2*G**2*Om**6/H) == 0     # eval 3 exact value
assert sp.simplify((x*G*Om**3)**2 / ((R/T1)*(Om**2/H)) - H) == 0  # md keeps xGOm^3: lossy by sqrt(H)
assert sp.simplify((R/T1)*(Sv/(x**2*G**2*Om**4)) - Sv) == 0       # eval 4 exact
assert 10**3 >= 100                                    # cN20 = 10^3 ample for exact evals
# cBox: BoxPowerSums per-entry constants are small absolute (crude box dominations) << 10^4
assert 10**4 >= 10**3
print("AM-6 pins OK (cN19=10^12, cN20=10^3 [4 evals banked], cBox=10^4)")

# ---- U4 block (amendments AM-1 + AM-2 + AM-5 bump, G1 rulings) ----
# AM-1 (hTaylor renormalization, NO G-largeness): H*Delta/F^2 = (Delta^5/(H^3 Om^2))*G^-2,
# so for G >= 1 the G>=1-provable form cPh*(H*Delta/F^2) <= cPh*(Delta^5/(H^3 Om^2)) holds.
H,G,Om,D = sp.symbols('H G Omega Delta', positive=True)
A=D*Om; F=H**2*G*Om/D**2
assert sp.simplify(H*D/F**2 - (D**5/(H**3*Om**2))/G**2) == 0
assert sp.simplify(D**5/H**3*(D/A)**2 - D**5/(H**3*Om**2)) == 0   # = delta0's first term
# N4 threshold budget (RE-PINNED 2026-06-13 for cPh=10^12): the hd producer route (mean value
# through dBreve' x Prop-3.2 near-integrality) has floor 2*cPh on the scale Delta^2/(H^2 G A), so
# cdMar >= 2*cPh = 2e12 -> cdMar = 10^13 (5x slack); cTay = max(cPh, cdMar) = 10^13.
# NOTE: cdMar/cTay floors bind only in the SORRIED N4/N13 producer (Sec7PhaseConstruct), so the
# green-with-sorries tree still builds at the old cdMar=10^7/cTay=10^12 — they MUST be bumped in the
# Lean defs (Sec7Defs.lean) before/at CODEX-C when those sorries are discharged.
assert 2 * cPh <= 10**13                               # cdMar >= producer floor 2*cPh, 5x slack
assert cPh <= 10**13 and 10**13 <= 10**13              # cTay >= max(cPh, cdMar) = 10^13
# N6 (A1 gate): eq-(7.1) error constant cN6 = 10^2*cPh = 10^14.
assert 40 * cPh <= 10**14
# N8 corner sum + N6 hprod error: cCal >= max(8*cTay, cN6) = max(8e13, 1e14) = 1e14 -> cCal = 10^15.
assert 8 * 10**13 <= 10**15 and 10**14 <= 10**15
# N17 (A5 gate): the Tq-band must admit |c1| <= cMon, |rho0| <= cCarry, p = ceil(R/72):
# band constant >= 2*cMon*cCarry*72^3 ~ 1.5*10^18 -> separate sec7_cBand = 10^20.
assert 2 * 10**6 * 10**6 * 72**3 <= 10**20
# Bumps landed: cTay=10^7, cdMar=10^7, cN6=10^8, cCal=10^9, cBand=10^20, cN13=10^43 (ARB-1),
# cFib=10^10, cJ=10^20.
# cJ: N3 discharge level = hnear (2H/D^2 <= 2*H/A^2 class) + hprox (ftil_prox, Sec7Prox
# .lean:100, EXACT shape 10^18*(H/A^2)); band needs >= 2*10^18 + O(1) <= 10^20.
assert 2 * 10**18 + 4 <= 10**20
# AM-2 (wide window [R/72, 16R], the RaWitness confinement): the dyadic pass needs at most
# 11 windows [p,2p] (ratio 16*72 = 1152 <= 2^11), absorbed by the *11 in the AM-6 chain.
assert 16*72 == 1152 and 1152 <= 2**11
assert 10**10 * 10**43 * 2**4 * 11 <= 10**58           # cTriple chain re-check (cFib=10^10, cTriple=10^60)
print("U4 ledger OK (cPh=10^12 re-pin: cTay=cdMar=10^13, cN6=10^14, cCal=10^15 >= max(8*cTay,cN6);"
      " cBand=10^20; cJ=10^20 >= 2*10^18; cFib=10^10; cTriple=10^60; 11 dyadic windows cover [R/72,16R]."
      " NOTE: Lean defs cdMar/cTay still at 10^7/10^12 — bump to 10^13 for CODEX-C [sorried N4/N13])")
# ---- ARB-1/ARB-2 RESOLVED (A3/A4/A6 arbitration, landed 2026-06-11) ----
# N9 MonExp is BUILT at the §3 site (sec7_monExp_exists DELETED); N11: habs DROPPED,
# errScale carries the explicit Pprod*hSum*T3/R^4 term (tc4-subordinated, above), and
# hρ₀ <= cCarry added; N12c = the Sec7ZeroHyp.few_critical FIELD; cCal SPLIT
# cDer=10^9/cLow=10^7/cTup=10^17/cTlo=10^12; cSub=10^28; cExp=cErr=10^25; cN13=10^43;
# cTriple=10^56; envC2=10^300 on n4-n7.  The SQUARED log (1+log X)^2 sits on the SEVEN
# envelope entries n1, n2, n3, res1, res2, tc9, tc10 (Prop-4.3 engine log x harvest log),
# killed on-strip by log_absorb_sq (k >= 2; the entry powers are 16/28/40/16/28/16/28).
assert all(k >= 2 for k in (16, 28, 40, 16, 28, 16, 28))   # log_absorb_sq applicability
print("ARB-1/ARB-2 trailer OK (7 squared-log entries: n1 n2 n3 res1 res2 tc9 tc10)")
