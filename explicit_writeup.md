
# Squarefree numbers in intervals of length \(X^{1/5-2/94885+\varepsilon}\)

## Theorem

For every \(g\) with \(0<g<2/18977\) there exists \(u=u(g)>0\) such that the following holds for all sufficiently large \(X\).

Set
\[
H:=X^{(1-g)/5},\qquad G:=X/H^5=X^g,\qquad U:=X^u.
\]
Then
\[
\sum_{X\le n\le X+H}\mu^2(n)=\frac{6}{\pi^2}H+O(H/U).
\]

Throughout, a factor \(X^{O(u)}\) means \(X^{Cu}\) for some absolute constant \(C\). Thus if a quantity is
\[
X^{\alpha(g)+O(u)}
\]
with \(\alpha(g)<0\), then it is \(O(U^{-1})\) once \(u<-\alpha(g)/(2C+2)\).

In particular, for every \(\varepsilon>0\), every sufficiently large \(X\) contains a squarefree number in
\[
[X,\ X+X^{1/5-2/94885+\varepsilon}].
\]

---

## 1. Initial reduction

For \(S\subset\mathbf N\), write
\[
\mathcal D(S):=\{d\in S:\exists m\in\mathbf Z,\ md^2\in[X,X+H]\}.
\]
Let
\[
\mathcal D:=\mathcal D(\mathbf N),\qquad \mathcal D[D,2D]:=\mathcal D((D,2D]).
\]
Let
\[
D_-:=H/U,\qquad D_+:=2X^{1/2}.
\]
Then
\[
\sum_{X\le n\le X+H}\mu^2(n)
=
\sum_{d\le D_+}\mu(d)\sum_{\substack{X\le n\le X+H\\ d^2\mid n}}1.
\]
For \(d\le D_-\),
\[
\sum_{\substack{X\le n\le X+H\\ d^2\mid n}}1=\frac{H}{d^2}+O(1),
\]
and for \(d>D_-\), since \(d^2>H\), the inner sum is \(O(1)\). Hence
\[
\sum_{X\le n\le X+H}\mu^2(n)
=
\sum_{d\le D_-}\mu(d)\Bigl(\frac{H}{d^2}+O(1)\Bigr)
+O\!\Bigl(\sum_{D_-\ll D\ll D_+}\#\mathcal D[D,2D]\Bigr),
\]
where \(D\) runs over dyadic scales. Therefore
\[
\sum_{X\le n\le X+H}\mu^2(n)
=
\frac{6}{\pi^2}H
+O\!\Bigl(D_-+\frac{H}{D_-}+\sum_{D_-\ll D\ll D_+}\#\mathcal D[D,2D]\Bigr).
\]
Since \(D_-=H/U\), the first two error terms are \(O(H/U)\). It remains to show
\[
\#\mathcal D[D,2D]\ll H/U
\]
for every dyadic \(D\) with \(H/U\ll D\ll X^{1/2}\).

Fix such a dyadic \(D\). Write
\[
\Delta:=\frac{D}{H}.
\]

---

## 2. The short-\(\Delta\) range

### Lemma 2.1
Let \(N\ge2\), \(0<\delta<1/4\), and let \(f\in C^4([N,3N])\) satisfy
\[
|f^{(4)}(x)|\asymp \Lambda \qquad (x\in[N,3N]).
\]
Then
\[
\#\{n\in(N,2N]\cap\mathbf Z:\|f(n)\|\le\delta\}
\ll
N^{7/8}+N\delta^{1/8}+N^{7/8}\Bigl(\frac{\delta}{\Lambda}\Bigr)^{1/8}
+\Lambda^{1/15}N.
\]

#### Proof
Set
\[
S:=\{n\in(N,2N]\cap\mathbf Z:\|f(n)\|\le\delta\},\qquad M:=\#S.
\]
If \(M\le1\) there is nothing to prove, so assume \(M\ge2\).

For a finite set \(A\subset\mathbf Z\), define
\[
r_A(h):=\#\{n\in A:n+h\in A\}.
\]

### Lemma 2.2
If \(A\subset(N,2N]\cap\mathbf Z\) has cardinality \(m\ge2\), then there exists \(h\) with
\[
1\le h\le \frac{4N}{m}+1
\]
such that
\[
r_A(h)\ge \frac{m^2}{16N}.
\]

#### Proof
Write \(A=\{a_1<\dots<a_m\}\). At least \(m/2\) of the consecutive gaps \(a_{j+1}-a_j\) are \(\le4N/m\); otherwise the total length would exceed \(N\). Hence
\[
\sum_{1\le h\le 4N/m+1} r_A(h)\ge \frac m2.
\]
Averaging over \(h\) yields the claim. ∎

Apply Lemma 2.2 three times. Starting with \(A_0:=S\), \(m_0:=M\), choose \(h_1\) and
\[
A_1:=A_0\cap(A_0-h_1),\qquad m_1:=\#A_1\ge \frac{M^2}{16N}.
\]
Then choose \(h_2\) and
\[
A_2:=A_1\cap(A_1-h_2),\qquad m_2:=\#A_2\ge \frac{m_1^2}{16N}.
\]
Then choose \(h_3\) and
\[
A_3:=A_2\cap(A_2-h_3),\qquad m_3:=\#A_3\ge \frac{m_2^2}{16N}.
\]
Therefore
\[
m_3\gg \frac{M^8}{N^7}.
\]
Also
\[
h_1\ll \frac{N}{M},\qquad h_2\ll \frac{N^2}{M^2},\qquad h_3\ll \frac{N^4}{M^4},
\]
so with \(P:=h_1h_2h_3\),
\[
P\ll \frac{N^7}{M^7}.
\]

For every \(n\in A_3\), all eight points
\[
n+\varepsilon_1h_1+\varepsilon_2h_2+\varepsilon_3h_3\qquad (\varepsilon_i\in\{0,1\})
\]
lie in \(S\). Hence
\[
\|\Delta_{h_1,h_2,h_3}f(n)\|\le 8\delta.
\]
Set
\[
g(x):=\Delta_{h_1,h_2,h_3}f(x).
\]
By the integral formula for finite differences,
\[
g'(x)=h_1h_2h_3\int_{[0,1]^3} f^{(4)}(x+t_1h_1+t_2h_2+t_3h_3)\,dt_1dt_2dt_3,
\]
so
\[
|g'(x)|\asymp P\Lambda,
\]
and \(g'\) has constant sign. Also
\[
\sup_{x\in[N,2N]}g(x)-\inf_{x\in[N,2N]}g(x)\ll P\Lambda N.
\]

By the one-dimensional counting lemma below, applied to \(g\),
\[
m_3\ll (P\Lambda N+1)\Bigl(1+\frac{\delta}{P\Lambda}\Bigr)
\ll 1+P\Lambda N+N\delta+\frac{\delta}{P\Lambda}.
\]
Since \(m_3\gg M^8/N^7\) and \(P\ll N^7/M^7\), at least one of the following holds:
\[
\frac{M^8}{N^7}\ll 1,\qquad
\frac{M^8}{N^7}\ll \frac{\Lambda N^8}{M^7},\qquad
\frac{M^8}{N^7}\ll N\delta,\qquad
\frac{M^8}{N^7}\ll \frac{\delta}{\Lambda}.
\]
These give respectively
\[
M\ll N^{7/8},\qquad
M\ll \Lambda^{1/15}N,\qquad
M\ll N\delta^{1/8},\qquad
M\ll N^{7/8}\Bigl(\frac{\delta}{\Lambda}\Bigr)^{1/8}.
\]
This proves the lemma. ∎

### Lemma 2.3
Let \(I\) be an interval, let \(\varphi:I\to\mathbf R\) be \(C^1\), suppose that
\[
\sup_I\varphi-\inf_I\varphi\ll V,\qquad |\varphi'(x)|\asymp F\quad(x\in I).
\]
Then, uniformly for \(0<\delta<1\),
\[
\sum_{n\in I\cap\mathbf Z}1_{\|\varphi(n)\|\le\delta}\ll (V+1)\Bigl(1+\frac{\delta}{F}\Bigr).
\]

#### Proof
For each integer \(m\), the preimage \(\varphi^{-1}([m-\delta,m+\delta])\) has length \(O(\delta/F)\). Since \(\varphi\) varies over an interval of length \(O(V)\), there are \(O(V+1)\) relevant integers \(m\). The count of integers in each preimage is \(O(1+\delta/F)\). ∎

### Proposition 2.4
If \(\Delta\le X^{1/100}\), then
\[
\#\mathcal D[D,2D]\ll H/U
\]
for \(u>0\) sufficiently small in terms of \(g\).

#### Proof
Let
\[
\mathcal E(D):=\{d\in(D,2D]\cap\mathbf Z:\exists m\in\mathbf Z,\ md^2\in[X,X+H]\}.
\]
If \(d\in\mathcal E(D)\), then
\[
\left\|\frac{X}{d^2}\right\|\le \frac{H}{d^2}\le \frac{H}{D^2}.
\]
Apply Lemma 2.1 with
\[
f(x)=\frac{X}{x^2},\qquad N=D,\qquad \delta=\frac{H}{D^2},\qquad \Lambda\asymp \frac{X}{D^6}.
\]
This gives
\[
\#\mathcal E(D)\ll D^{7/8}+H^{1/8}D^{3/4}+X^{-1/8}H^{1/8}D^{11/8}+X^{1/15}D^{3/5}.
\]
Now \(D=H\Delta\le HX^{1/100}\), so each term is
\[
\ll X^\kappa
\]
with
\[
\kappa<\frac{1-g}{5}
\]
for all \(g<2/18977\). Hence each term is \(X^{(1-g)/5-c(g)}\) for some \(c(g)>0\), and therefore \(O(H/U)\) once \(u<c(g)/2\). ∎

From now on assume
\[
\Delta\ge X^{1/100}.
\]

---

## 3. Structural reduction in the variable \(d\)

Define
\[
\mathcal D_a:=\{d:d,d+a\in \mathcal D,\ (d,d+a)\cap \mathcal D=\varnothing\}.
\]
By a dyadic pigeonhole decomposition in the gap parameter \(a\), and by the lower bound \(\#\mathcal D[D,2D]\ge H/U\) in the only cases of interest, one has
\[
\#\mathcal D[D,2D]\ll \sum_{1\ll A\ll \Delta U}\ \sum_{a\sim A}\#\mathcal D_a.
\]
Also, by the Nair-Roth observation that among any three consecutive elements of \(\mathcal D\) two are spaced by
\[
\gg \Delta^{4/3}(H^4/X)^{1/3},
\]
one may discard the smaller dyadic scales and replace this by
\[
\#\mathcal D[D,2D]\ll \sum_{1+\Delta^{4/3}(H^4/X)^{1/3}\ll A\ll \Delta U}\ \sum_{a\sim A}\#\mathcal D_a.
\]
From now on we fix such a dyadic scale \(A\).

### Lemma 3.1
If \(d<d+b\) lie in \(\mathcal D_a\) and \((d,d+b)\cap \mathcal D_a\neq \varnothing\), then
\[
b\gg a^{-1/3}\Delta^{5/3}(H^5/X)^{1/3}.
\]

#### Proof
Choose integers \(m_1,m_2,m_3,m_4\) such that
\[
m_1d^2,\ m_2(d+a)^2,\ m_3(d+b)^2,\ m_4(d+a+b)^2\in [X,X+H].
\]
Since \((d,d+a)\cap \mathcal D=\varnothing\) and there exists \(d'\in \mathcal D_a\cap(d,d+b)\), one has \(d'\ge d+a\). Also \(d+b\in \mathcal D\) and \((d',d'+a)\cap \mathcal D=\varnothing\), so necessarily \(d+b\ge d'+a\). Hence
\[
b\ge 2a.
\]
Now form the integer
\[
J:=-(b-a)m_1+(b+a)m_2-(b+a)m_3+(b-a)m_4.
\]
By construction,
\[
J=S_{a,b}(d)+O\!\left((a+b)\frac{H}{D^2}\right),
\]
where
\[
S_{a,b}(d)=-(b-a)\frac{X}{d^2}+(b+a)\frac{X}{(d+a)^2}-(b+a)\frac{X}{(d+b)^2}+(b-a)\frac{X}{(d+a+b)^2}.
\]
A direct simplification gives the exact factorization
\[
S_{a,b}(d)=\frac{Xab(a-b)(a+b)(a+b+2d)(ab+2ad+2bd+2d^2)}{d^2(d+a)^2(d+b)^2(d+a+b)^2}.
\]
Since \(a\ll \Delta U\ll D/H^{1/2}\), and since in the contrary range under consideration one has
\[
b\le c_0\, a^{-1/3}\Delta^{5/3}(H^5/X)^{1/3}\ll D,
\]
again because \(a\sim A\gg \Delta^{4/3}(H^4/X)^{1/3}\) and \(D=H\Delta\),
all denominator factors are \(\asymp D^2\), while \(|a-b|\asymp b\), \(a+b\asymp b\), \(a+b+2d\asymp D\), and \(ab+2ad+2bd+2d^2\asymp D^2\). Hence
\[
|S_{a,b}(d)|\asymp \frac{Xab^3}{D^5}.
\]
Therefore, if
\[
b\le c_0\, a^{-1/3}\Delta^{5/3}(H^5/X)^{1/3}
\]
with \(c_0>0\) sufficiently small, then \(|S_{a,b}(d)|<1/2\). On the other hand,
\[
\frac{(a+b)H/D^2}{|S_{a,b}(d)|}\ll \frac{D^3H}{Xab^2}\ll \frac{D^3H}{Xa^3}\ll \frac1\Delta,
\]
using \(b\ge 2a\) and the lower bound \(a\sim A\gg \Delta^{4/3}(H^4/X)^{1/3}\). For sufficiently large \(X\), this gives
\[
0<|J|<1,
\]
contradicting the integrality of \(J\). Hence the displayed upper bound for \(b\) is impossible. ∎

Define Roth's differencing quantity
\[
R_a(d)=-(2d-a)\frac{X}{d^2}+(2d+3a)\frac{X}{(d+a)^2}.
\]
Also set
\[
F_a(d):=\frac{X}{d^2}-\frac{X}{(d+a)^2}.
\]
Its expansion is
\[
R_a(d)=\frac{Xa^3}{d^2(d+a)^2}
=\frac{Xa^3}{d^4}\Bigl(1-2a/d+O((a/d)^2)\Bigr).
\]
Write
\[
R:=\frac{XA^3}{\Delta^4H^4}=\frac{HG\Omega^3}{\Delta},\qquad \widetilde d_a:=R_a^{-1}.
\]
Then for \(\rho\asymp R\),
\[
\widetilde d_a^{(j)}(\rho)\asymp \frac{H\Delta}{R^j}\qquad (j\ge0).
\]

### Proposition 3.2
For each \(a\sim A\) there is a set \(\mathcal R_a\subset\mathbf N\) with \(r\asymp R\) for every \(r\in \mathcal R_a\) and a map
\[
d_a^*:\mathcal R_a\to \mathcal D_a
\]
such that
\[
\frac{\#\mathcal D_a}{\#\mathcal R_a}\ll 1+\Bigl(\frac{\Delta}{A}\Bigr)^{8/3}G^{-2/3},
\]
and
\[
d_a^*(r)=\widetilde d_a(r)+O\!\left(\frac{\Delta}{G}\frac{\Delta^3}{A^3}\right).
\]

#### Proof
For each \(d\in \mathcal D_a\), choose the unique integer \(r_a^*(d)\asymp R\) such that
\[
R_a(d)=r_a^*(d)+O(1/\Delta).
\]
If \(r_a^*(d_1)=\dots=r_a^*(d_k)\), then
\[
|R_a(d_1)-R_a(d_k)|\ll 1/\Delta.
\]
Write the fiber in increasing order, \(d_1<\cdots<d_k\). Then the subsequence \(d_1,d_3,d_5,\dots\) consists of pairwise non-consecutive elements of \(\mathcal D_a\), so Lemma 3.1 gives
\[
|d_1-d_k|\gg k\,A^{-1/3}\Delta^{5/3}(H^5/X)^{1/3}.
\]
Since \(R_a'(d)\asymp XA^3/D^5\) on \(d\asymp D\), the mean value theorem yields
\[
|R_a(d_1)-R_a(d_k)|
\asymp \frac{XA^3}{(H\Delta)^4}\cdot \frac{|d_1-d_k|}{H\Delta}
\gg \frac{k}{\Delta}\Bigl(\frac{A}{\Delta}\Bigr)^{8/3}G^{2/3}.
\]
Therefore
\[
k\ll 1+\Bigl(\frac{\Delta}{A}\Bigr)^{8/3}G^{-2/3}.
\]
Take \(\mathcal R_a:=r_a^*(\mathcal D_a)\) and let \(d_a^*\) be any left inverse. The stated preimage bound follows.

For the approximation, if \(r\in \mathcal R_a\), then
\[
r=R_a(d_a^*(r))+O(1/\Delta).
\]
Since \(R_a'(\widetilde d_a(r))\asymp R/(H\Delta)\), solving by one Newton step gives
\[
d_a^*(r)=\widetilde d_a(r)\Bigl(1+O\Bigl(\frac{1}{R\Delta}\Bigr)\Bigr)
=\widetilde d_a(r)+O\!\left(\frac{\Delta}{G}\frac{\Delta^3}{A^3}\right).
\]
∎

Write
\[
\Omega:=\frac{A}{\Delta}.
\]
The trivial bound from Proposition 3.2 shows that the contribution of
\[
\Omega\ll G^{-1/4}U^{-3/4}
\]
is \(O(H/U)\). Hence from now on
\[
G^{-1/4}U^{-3/4}\ll \Omega\ll U.
\]

---

## 4. Elementary point-near-curve lemmas

### Lemma 4.1
Let \(I\) be an interval and let \(\varphi:I\to\mathbf R\) satisfy
\[
\sup_I\varphi-\inf_I\varphi\ll V,\qquad |\varphi'(x)|\asymp F\quad(x\in I).
\]
Then
\[
\sum_{n\in I\cap\mathbf Z}1_{\|\varphi(n)\|\le \delta}\ll (V+1)\Bigl(1+\frac{\delta}{F}\Bigr).
\]

#### Proof
This is Lemma 2.3. ∎

### Lemma 4.2
Let \(I\subset[c_1N,c_2N]\) for fixed \(0<c_1<c_2\). Suppose \(\varphi:I\to\mathbf R\) satisfies
\[
|\varphi'(x)|\ll \frac{T}{N},\qquad |\varphi'(x)|+N|\varphi''(x)|\asymp \frac{T}{N}
\]
for all \(x\in I\). Assume further that \(\varphi'\) and \(\varphi''\) each have \(O(1)\) zeros. Then
\[
\sum_{n\in I\cap\mathbf Z}1_{\|\varphi(n)\|\le\delta}
\ll
N\Bigl(\delta+\sqrt{\delta/T}\Bigr)+T+1.
\]

#### Proof
Split \(I\) into \(O(1)\) intervals on which \(\varphi''\) has constant sign. On such an interval, define
\[
I_>:=\{x:|\varphi'(x)|\ge cT/N\},
\]
\[
I_k:=\{x:ce^{-k}T/N\le |\varphi'(x)|<ce^{-k+1}T/N\}\qquad(1\le k\le K),
\]
\[
I_<:=\{x:|\varphi'(x)|<ce^{-K}T/N\},
\]
with \(K=\lceil \tfrac12\log(T/\delta)\rceil\) and \(c>0\) small. By the lower bound on \(|\varphi''|\) wherever \(|\varphi'|\) is small, one has
\[
|I_k|\ll e^{-k}N,\qquad |I_<|\ll e^{-K}N.
\]
Also \(\varphi\) varies by \(O(e^{-2k}T)\) on \(I_k\), and by \(O(e^{-2K}T)\) on \(I_<\). Applying Lemma 4.1 on each \(I_k\), and the trivial estimate on \(I_<\), gives
\[
\sum_{n\in I\cap\mathbf Z}1_{\|\varphi(n)\|\le\delta}
\ll
N\delta + e^K\frac{\delta N}{T}+T+1
\ll
N\Bigl(\delta+\sqrt{\delta/T}\Bigr)+T+1.
\]
∎

### Proposition 4.3
Let \(F:[1/2,5/2]\to\mathbf R\) satisfy \(|F''(x)|\asymp 1\). Then for all \(T,N>1\) and \(0<\delta<1\),
\[
\#\Bigl\{n\sim N:\|TF(n/N)\|\le\delta\Bigr\}
\ll
(NT)^{1/3}+N\delta+N\sqrt{\delta/T}\log\!\Bigl(2+N\sqrt{\delta/T}\Bigr)+1.
\]

#### Proof
Set
\[
f(x):=TF(x/N),\qquad \lambda:=\frac{T}{N^2}.
\]
Then \(|f''(x)|\asymp \lambda\) on \([N/2,5N/2]\), and it suffices to show that for
\[
S:=\{n\in[N,2N]\cap \mathbf Z:\|f(n)\|\le \delta\}
\]
one has
\[
\#S\ll N\lambda^{1/3}+N\delta+\sqrt{\delta/\lambda}\log\!\Bigl(2+\sqrt{\delta/\lambda}\Bigr)+1.
\]
If \(\delta\ge 1/2\), this is trivial because \(\#S\le N\ll N\delta\). Hence we may assume \(\delta<1/2\). For each \(n\in S\), let \(\ell_n\in \mathbf Z\) be the unique nearest integer to \(f(n)\), and set
\[
M_n:=(n,\ell_n)\in \mathbf Z^2.
\]

If \(n_0<n_1<n_2\) lie in \(S\) and the three lattice points \(M_{n_0},M_{n_1},M_{n_2}\) are not collinear, then
\[
n_2-n_0\gg \min(\lambda^{-1/3},\delta^{-1}).
\]
Indeed, write
\[
f(n_i)=\ell_{n_i}+\varepsilon_i,\qquad |\varepsilon_i|\le \delta.
\]
Let \(Q\) be the quadratic interpolation polynomial through the points \((n_i,\ell_{n_i})\), and let \(u\neq 0\) be the numerator of its quadratic coefficient. Then
\[
\frac{u}{(n_1-n_0)(n_2-n_1)(n_2-n_0)}
\]
is the quadratic coefficient of \(Q\). By the divided-difference formula, the quadratic coefficient of the interpolation polynomial through \((n_i,f(n_i))\) is \(f''(\xi)/2\) for some \(\xi\in[n_0,n_2]\). Hence
\[
\frac{u}{(n_1-n_0)(n_2-n_1)(n_2-n_0)}
=
\frac{f''(\xi)}{2}
+O\!\left(
\delta\sum_{i=0}^2\frac{1}{\prod_{j\neq i}|n_i-n_j|}
\right).
\]
If \(L:=n_2-n_0\), then \((n_1-n_0)(n_2-n_1)(n_2-n_0)\ll L^3\), while after multiplying through by this product the error contributes \(O(\delta L)\). Since \(|u|\ge 1\), we obtain
\[
1\ll \lambda L^3+\delta L,
\]
which implies the displayed spacing bound.

A major arc is a connected component of the intersection of the strip
\[
\{(x,y):|f(x)-y|\le \delta\}
\]
with a rational line \(y=P(x)\), provided that this component contains at least three lattice points \(M_n\). If \(q\) is the least positive integer with \(P\in q^{-1}\mathbf Z[X]\), we call \(q\) the denominator of the arc, and write \(\nu(A)\) for the number of lattice points on the arc \(A\).

If \(A\) is a major arc on a line of denominator \(q\), and \(L\) is the length of its projection to the \(x\)-axis, then
\[
\nu(A)\ll \frac{L}{q},\qquad q\ll L,\qquad L\ll \sqrt{\delta/\lambda}.
\]
The first two facts hold because the lattice points on the line have \(x\)-coordinates all congruent modulo \(q\), and \(A\) contains at least three of them. For the third, write \(g(x):=f(x)-P(x)\). On the projected interval \([a,a+L]\) of \(A\), one has \(|g(x)|\le \delta\) and \(|g''(x)|\asymp \lambda\). If \(m=a+L/2\), then
\[
g(a)-2g(m)+g(a+L)=\frac{L^2}{4}g''(\xi)
\]
for some \(\xi\in[a,a+L]\). The left-hand side is \(O(\delta)\), so \(L^2\lambda\ll \delta\).

Also, since \(g'\) is monotone, the strip-line intersection has at most two connected components on any fixed rational line. For each line we therefore choose one component with maximal \(\nu(A)\), and call it the proper major arc of that line. The total number of lattice points lying on major arcs is then at most twice the total over proper major arcs.

Now let \(A\) be a proper major arc on the line \(y=P(x)\), with denominator \(q\le c/\delta\) for a sufficiently small absolute constant \(c>0\). Let \(L\) be its projected length, and let \(M_{m_0}\in A\). If \(M_m\in S\) does not lie on the line \(y=P(x)\), then
\[
|m-m_0|\gg \min\!\left(\frac{L}{q\delta},\frac{1}{q\lambda L},\frac{1}{\sqrt{q\lambda}}\right).
\]
To prove this, again write \(g=f-P\). Since \(|g|\le \delta\) on the projected interval of \(A\), there is some point \(\xi\) in that interval with \(|g'(\xi)|\ll \delta/L\). Hence
\[
|g'(m_0)|\ll \frac{\delta}{L}+\lambda L.
\]
If \(P(m)\notin \mathbf Z\), then the distance from \(P(m)\) to the nearest integer is at least \(1/q\), so
\[
|g(m)|=|f(m)-P(m)|\ge \frac1q-\delta\gg \frac1q
\]
because \(q\le c/\delta\). If \(P(m)\in \mathbf Z\), then \(M_m\) not lying on the line means \(P(m)\neq \ell_m\), and therefore
\[
|g(m)|=|f(m)-P(m)|\ge \frac12\gg \frac1q.
\]
Since \(|g(m_0)|\le \delta\ll 1/q\), in either case
\[
|g(m)-g(m_0)|\gg \frac{1}{q}.
\]
Taylor expansion at \(m_0\) yields
\[
g(m)-g(m_0)=(m-m_0)g'(m_0)+O\!\left(\lambda (m-m_0)^2\right),
\]
and therefore
\[
\frac{1}{q}\ll |m-m_0|\left(\frac{\delta}{L}+\lambda L\right)+\lambda |m-m_0|^2.
\]
This gives the claimed lower bound.

We now count the residual points, namely
\[
S_{\mathrm{res}}:=\{n\in S:M_n\text{ lies on no major arc of denominator }\le c/\delta\}.
\]
Take any five consecutive points \(n_1<\cdots<n_5\) of \(S_{\mathrm{res}}\). If they are not all collinear, then some triple among them is non-collinear, and the first spacing bound gives
\[
n_5-n_1\gg \min(\lambda^{-1/3},\delta^{-1}).
\]
If they are all collinear, then either the supporting line has denominator \(>c/\delta\), in which case
\[
n_5-n_1\ge 4q\gg \delta^{-1},
\]
or else the line has denominator \(\le c/\delta\). But a strip-line intersection has at most two connected components, so five collinear points on such a line force one component to contain at least three lattice points, contradicting the definition of \(S_{\mathrm{res}}\). Hence every five consecutive residual points span \(\gg \min(\lambda^{-1/3},\delta^{-1})\), and so
\[
\#S_{\mathrm{res}}\ll N\lambda^{1/3}+N\delta+1.
\]

It remains to count the major-arc contribution. Split the proper major arcs with denominator \(q\le c/\delta\) into two classes.

Type I consists of those arcs for which
\[
L\le \delta\sqrt{q/\lambda}.
\]
For such an arc, the first term in the spacing bound is the smallest one, so every lattice point of \(S\) not on the supporting line of \(A\) is at distance
\[
\gg d(A):=\frac{L}{q\delta}
\]
from every point of \(A\). Since \(q\le c/\delta\), one has \(d(A)\gg L\). Order the type I proper arcs by their first \(x\)-coordinate \(n_j\), and attach to each the interval
\[
I_j:=[n_j,n_j+c_1d(A_j)]
\]
with \(c_1>0\) sufficiently small. If \(j<k\), then the first lattice point of \(A_k\) does not lie on the supporting line of \(A_j\), so the spacing bound gives
\[
n_k-n_j\gg d(A_j).
\]
Thus the intervals \(I_j\) are pairwise disjoint. Since
\[
\nu(A_j)\ll \frac{L_j}{q_j}=\delta\, d(A_j)\asymp \delta\,|I_j|,
\]
the total type I proper-arc contribution is
\[
\ll N\delta+1.
\]

Type II consists of the remaining proper major arcs, so
\[
L> \delta\sqrt{q/\lambda}.
\]
Since always \(L\ll \sqrt{\delta/\lambda}\) and \(q\ll L\), every type II arc satisfies
\[
q\ll \sqrt{\delta/\lambda}.
\]
Fix such a denominator \(q\), and fix a slope \(r/q\). Write
\[
h(x):=f(x)-\frac{r}{q}x.
\]
Then \(|h''(x)|\asymp \lambda\), so after replacing \(h\) by \(-h\) if necessary we may assume that \(h\) is convex. A type II arc on a line of slope \(r/q\) is a connected component of
\[
\left|h(x)-\frac{b}{q}\right|\le \delta
\]
for some integer \(b\). Let \(x_0\) be the point where \(h\) attains its minimum on \([N,2N]\), and write \(m:=h(x_0)\).

A type II component containing \(x_0\) must satisfy \(|b/q-m|\le \delta\), so there are only \(O(1)\) such possibilities because \(q\le c/\delta\). For the remaining components, the projection lies on one side of \(x_0\); assume it lies to the right, with projected interval \([u,v]\) and length \(L=v-u\). By the mean value theorem there exists \(\xi\in[u,v]\) with
\[
|h'(\xi)|\ll \delta/L.
\]
Since \(h'(x_0)=0\) and \(h''\asymp \lambda\), this implies
\[
\xi-x_0\ll \frac{\delta}{\lambda L}.
\]
Because \(u\le \xi\), we have \(u-x_0\ll \delta/(\lambda L)\), and therefore
\[
h(u)-m\ll \lambda (u-x_0)^2\ll \frac{\delta^2}{\lambda L^2}.
\]
But \(h(u)\ge b/q-\delta\), so
\[
\frac{b}{q}-m\ll \delta+\frac{\delta^2}{\lambda L^2}.
\]
Since \(L>\delta\sqrt{q/\lambda}\), the last term is \(O(1/q)\). Also \(b/q\ge m-\delta\) because the component is nonempty. Hence the admissible values of \(b/q\) lie in an interval of length \(O(\delta+1/q)\), which contains only \(O(q\delta+1)=O(1)\) possibilities because \(q\le c/\delta\). Thus for each fixed denominator \(q\) and slope \(r/q\), there are only \(O(1)\) type II proper arcs.

For each such arc, the mean value theorem also gives a point \(\xi\) in its projection with
\[
\left|f'(\xi)-\frac{r}{q}\right|=|h'(\xi)|\ll \delta/L\ll \sqrt{\delta\lambda/q}.
\]
Hence for fixed \(q\) the admissible slopes \(r/q\) lie in the \(O(\sqrt{\delta\lambda/q})\)-neighbourhood of the range of \(f'\), whose length is \(O(N\lambda)\). Since \(q\ll \sqrt{\delta/\lambda}\), this yields only
\[
O(qN\lambda+1)
\]
possible slopes \(r/q\). Each corresponding type II proper arc has
\[
\nu(A)\ll \frac{L}{q}+1\ll \frac{\sqrt{\delta/\lambda}}{q}+1.
\]
Hence the total type II proper-arc contribution is
\[
\ll
\sum_{q\ll \sqrt{\delta/\lambda}}
(qN\lambda+1)\left(\frac{\sqrt{\delta/\lambda}}{q}+1\right).
\]
Estimating the sums gives
\[
\ll
N\delta+\sqrt{\delta/\lambda}\log\!\Bigl(2+\sqrt{\delta/\lambda}\Bigr)+1.
\]

Finally, the total contribution from all major arcs is at most twice the total over proper major arcs. Combining this with the bounds for \(S_{\mathrm{res}}\), the type I proper arcs, and the type II proper arcs, we obtain
\[
\#S\ll N\lambda^{1/3}+N\delta+\sqrt{\delta/\lambda}\log\!\Bigl(2+\sqrt{\delta/\lambda}\Bigr)+1.
\]
Since \(\lambda=T/N^2\), this is exactly the claimed estimate. ∎

---

## 5. The range \(\Delta\ll H^{1/2}(GU)^{-O(1)}\)

The following propositions reproduce the elementary part of the argument.

\[
\mathcal R_a(\ell_1,\ell_2):=\{r\in \mathcal R_a:r,r+\ell_1,r+\ell_2\text{ are consecutive elements of }\mathcal R_a\}.
\]

For \(r\in \mathcal R_a(\ell_1,\ell_2)\), let \(d=d_a^*(r)\). Define \(b_0(r),v(r)\in \ell_1^{-1}\mathbf Z\) by
\[
d+\ell_1b_0=d_a^*(r+\ell_1),\qquad d+\ell_2b_0+v=d_a^*(r+\ell_2).
\]
Also define
\[
\widetilde b_a(r):=\frac{\widetilde d_a(r+\ell_1)-\widetilde d_a(r)}{\ell_1},
\qquad
B:=\frac{D}{R}\asymp \frac{\Delta^2}{G\Omega^3}.
\]
By Proposition 3.2,
\[
d_a^*(\rho)=\widetilde d_a(\rho)+O\!\left(\frac{\Delta}{G\Omega^3}\right)
\qquad (\rho\asymp R).
\]
Therefore
\[
b_0=\frac{d_a^*(r+\ell_1)-d_a^*(r)}{\ell_1}
=\widetilde b_a(r)+O\!\left(\frac{\Delta}{\ell_1G\Omega^3}\right).
\]
Since \(\widetilde d_a^{(j)}(\rho)\asymp D/R^j\), the discrete quotient defining \(\widetilde b_a\) has the same scale as \(\widetilde d_a'\), and repeated differentiation gives
\[
\widetilde b_a^{(j)}(\rho)\asymp \frac{B}{R^j}
\qquad (j\ge 0).
\]
Next,
\[
v=d_a^*(r+\ell_2)-\frac{\ell_2}{\ell_1}d_a^*(r+\ell_1)+\frac{\ell_2-\ell_1}{\ell_1}d_a^*(r).
\]
Replacing \(d_a^*\) by \(\widetilde d_a\), and using the approximation error from Proposition 3.2, gives
\[
v=\widetilde d_a(r+\ell_2)-\frac{\ell_2}{\ell_1}\widetilde d_a(r+\ell_1)+\frac{\ell_2-\ell_1}{\ell_1}\widetilde d_a(r)
+O\!\left(\Delta\frac{\ell_2}{\ell_1G\Omega^3}\right).
\]
A second-order Taylor expansion around \(r\) gives
\[
\widetilde d_a(r+\ell_2)-\frac{\ell_2}{\ell_1}\widetilde d_a(r+\ell_1)+\frac{\ell_2-\ell_1}{\ell_1}\widetilde d_a(r)
\ll \sup_{\rho\asymp R}|\widetilde d_a''(\rho)|\,\ell_2(\ell_2-\ell_1)
\ll \Delta\frac{\ell_2(\ell_2-\ell_1)}{R^2}.
\]
Since \(\ell_2\ll W\asymp GU^5\), this yields
\[
v\ll \Delta\left(\frac{W^2}{R^2}+\frac{W}{G\Omega^3}\right)
\ll \Delta\Bigl(\frac{\Delta^2U^{10}}{H\Omega^6}+\frac{U^5}{\Omega^3}\Bigr)
\ll \frac{\Delta U^5}{\Omega^3}.
\]

### Proposition 5.1
Assume
\[
\frac{H}{\Delta^2}\gg GU^{10},\qquad \Delta\gg G^2U^5.
\]
Let \(W\asymp GU^5\). If \(\#\mathcal R_a\ge R/W\), then
\[
\#\mathcal R_a\ll \frac{H}{\Delta}\left(\frac{G^9U^{51}}{\Delta^{1/2}\Omega}
+\frac{\Delta^2}{H}\frac{G^{17}U^{100}}{\Omega^{27}}
+\frac{G^{17}U^{85}}{\Delta\Omega^{13}}\right).
\]

#### Proof
Choose \(\ell_1<\ell_2\ll W\) with
\[
\#\mathcal R_a(\ell_1,\ell_2)\gg \#\mathcal R_a/W^2.
\]
We will bound \(\#\mathcal R_a(\ell_1,\ell_2)\) explicitly and then sum over the \(O(W^2)\) possible pairs \((\ell_1,\ell_2)\).

Set
\[
S_{a,b}(d)=-(b-a)\frac{X}{d^2}+(b+a)\frac{X}{(d+a)^2}-(b+a)\frac{X}{(d+b)^2}+(b-a)\frac{X}{(d+a+b)^2},
\]
\[
\widehat S_{a,b}(d):=S_{a,b}(d)-\bigl(R_a(d)-R_a(d+b)\bigr),
\]
\[
F_{a,b}(d):=F_a(d)-F_a(d+b).
\]
From the Taylor expansion
\[
\frac1{(d+x)^2}=\frac1{d^2}\left(1-2\frac{x}{d}+3\frac{x^2}{d^2}-4\frac{x^3}{d^3}+5\frac{x^4}{d^4}+O\!\left(\frac{x^5}{d^5}\right)\right)
\]
we obtain
\[
\widehat S_{a,b}(d)=\frac{X}{d^5}\left(-4ab^3+\frac{10ab^4+10a^2b^3}{d}+O\!\left(\frac{ab^5+a^2b^4+a^3b^3}{d^2}\right)\right),
\]
\[
F_{a,b}(d)=\frac{X}{d^4}\left(6ab-\frac{12a^2b+6ab^2}{d}+O\!\left(\frac{a^3b+a^2b^2+ab^3}{d^2}\right)\right).
\]
We also record the truncated form
\[
\widehat S_{a,b}(d)=\frac{X}{d^5}\left(\left(-4a+10\frac{a^2}{d}\right)\left(b^3-\frac{5}{2}\frac{b^4}{d}\right)+O\!\left(\frac{ab^5}{d^2}\right)\right),
\]
which is the version needed in the large-defect range.

Because \(d,d+a\in \mathcal D\) implies \(F_a(d)\in \mathbf Z+O(1/(H\Delta^2))\), we have
\[
\mathcal Q:=\ell_1F_{a,\ell_2b_0+v}(d)-\ell_2F_{a,\ell_1b_0}(d)
\in \mathbf Z+O\!\left(\frac{W}{H\Delta^2}\right)
\subset \mathbf Z+O\!\left(\frac1\Delta\right).
\]
Substituting the expansion of \(F_{a,b}\), and noting that the leading \(6ab\)-term cancels between the two copies of \(F_{a,b}\), gives
\[
\mathcal Q
=
6\ell_1\frac{Xav}{d^4}
-
12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa b_0^2}{d^5}
+
O\!\left(W^2\frac{Xab_0|v|}{d^5}+W^3\frac{Xab_0^3}{d^6}\right).
\]
Using \(b_0\asymp B\), \(|v|\ll \Delta U^5/\Omega^3\), \(d\asymp D\), and the identities
\[
\frac{XaB}{D^5}=\frac1{\Delta^2\Omega^2},
\qquad
\frac{XaB^3}{D^6}=\frac{\Delta}{HG^2\Omega^8},
\]
we obtain
\[
W^2\frac{Xab_0|v|}{d^5}\ll W^2\frac{|v|}{\Delta^2\Omega^2}
\ll \frac1\Delta\frac{G^2U^{15}}{\Omega^5},
\]
\[
W^3\frac{Xab_0^3}{d^6}\ll \frac{\Delta}{H}\frac{GU^{15}}{\Omega^8}
\ll \frac1\Delta\frac{G^2U^{15}}{\Omega^5},
\]
where the last step uses \(H/\Delta^2\gg GU^{10}\) and \(\Omega\gg G^{-1/4}U^{-3/4}\). Hence
\[
\mathcal Q
=
6\ell_1\frac{Xav}{d^4}
-
12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa b_0^2}{d^5}
+
O\!\left(\frac1\Delta\frac{G^2U^{15}}{\Omega^5}\right).
\]

**Step 1: the zero-defect range \(v=0\).**
If \(v=0\), then
\[
\mathcal Q=-12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa b_0^2}{d^5}+O\!\left(\frac1\Delta\frac{G^2U^{15}}{\Omega^5}\right).
\]
Replacing \(d\) and \(b_0\) by \(\widetilde d_a(r)\) and \(\widetilde b_a(r)\), and using
\[
b_0=\widetilde b_a(r)\left(1+O\!\left(\frac1{\ell_1\Delta}\right)\right),
\qquad
\widetilde d_a(r)=d+O\!\left(\frac{\Delta}{G\Omega^3}\right),
\]
we obtain
\[
\mathcal Q=-12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa\widetilde b_a(r)^2}{\widetilde d_a(r)^5}+O\!\left(\frac1\Delta\frac{G^3U^{10}}{\Omega^5}\right).
\]
Hence, with
\[
\varphi(r):=12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa\widetilde b_a(r)^2}{\widetilde d_a(r)^5},
\]
we have
\[
\|\varphi(r)\|\ll \frac1\Delta\frac{G^3U^{10}}{\Omega^5}.
\]
Now
\[
\varphi(\rho)\asymp \ell_1\ell_2(\ell_2-\ell_1)\frac{XaB^2}{D^5}
\asymp \ell_1\ell_2(\ell_2-\ell_1)\frac1{G\Omega^5}=:L,
\]
and every differentiation in \(\rho\) costs a factor \(1/R\), so
\[
|\varphi'(\rho)|\asymp \frac{L}{R}
\qquad (\rho\asymp R).
\]
Lemma 4.1 therefore gives
\[
\#\{r\in \mathcal R_a(\ell_1,\ell_2):v(r)=0\}
\ll L+R\frac1\Delta\frac{G^3U^{10}}{\Omega^5}.
\]
Since \(L\ll G^2U^{15}/\Omega^5\) and \(R\asymp HG\Omega^3/\Delta\), the second term equals
\[
\frac{H}{\Delta^2}\frac{G^4U^{10}}{\Omega^2},
\]
and the first is absorbed into it by \(H/\Delta^2\gg GU^{10}\). Thus
\[
\#\{r\in \mathcal R_a(\ell_1,\ell_2):v(r)=0\}
\ll \frac{H}{\Delta^2}\frac{G^4U^{10}}{\Omega^2}.
\]

**Step 2: the general small-defect range \(0<|v|\le V_+\).**
Assume
\[
\frac{\Delta^3}{H}\ll V_+\ll \frac{\Delta^3}{H}\frac{U^{10}}{\Omega^6}.
\]
For \(|v|\le V_+\), the formula for \(\mathcal Q\) gives
\[
|\mathcal Q|\ll G^2U^5\Omega\frac{HV_+}{\Delta^3}+\frac{G^2U^{15}}{\Omega^5}
\ll \frac{G^2U^{15}}{\Omega^5}.
\]
Since \(\mathcal Q\in \mathbf Z+O(1/\Delta)\), there exists an integer
\[
|f|\ll G^2U^5\Omega\frac{HV_+}{\Delta^3}+\frac{G^2U^{15}}{\Omega^5}
\ll \frac{G^2U^{15}}{\Omega^5}
\]
such that
\[
6\ell_1\frac{Xav}{\widetilde d_a(r)^4}
=
f+12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa\widetilde b_a(r)^2}{\widetilde d_a(r)^5}
+O\!\left(\frac1\Delta\frac{G^2U^{20}}{\Omega^5}\right).
\]
Multiplying by \(\widetilde d_a(r)^4/(6\ell_1Xa)\), we obtain
\[
v=
\frac{\widetilde d_a(r)^4}{6\ell_1Xa}
\left(f+12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa\widetilde b_a(r)^2}{\widetilde d_a(r)^5}\right)
+O\!\left(\frac{\Delta^2}{H}\frac{GU^{20}}{\ell_1\Omega^6}\right).
\]
Because \(v\in \ell_1^{-1}\mathbf Z\), the phase
\[
\varphi_f(r):=\frac{\widetilde d_a(r)^4}{6Xa}
\left(f+12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa\widetilde b_a(r)^2}{\widetilde d_a(r)^5}\right)
\]
satisfies
\[
\|\varphi_f(r)\|\ll \delta:=\frac{\Delta^2}{H}\frac{GU^{20}}{\Omega^6}.
\]
Now
\[
\frac{\widetilde d_a(r)^4}{Xa}\asymp \frac{D^4}{Xa}=\frac{\Delta^3}{HG\Omega},
\qquad
\frac{\widetilde b_a(r)^2}{\widetilde d_a(r)}\asymp \frac{B^2}{D}=\frac{\Delta^3}{HG^2\Omega^6},
\]
and again each derivative costs a factor \(1/R\). Therefore
\[
|\varphi_f'(\rho)|+R|\varphi_f''(\rho)|\asymp \frac{T}{R},
\]
with
\[
T:=\frac{\Delta^3}{H}\max\!\left(\frac{|f|}{G\Omega},\ell_1\ell_2(\ell_2-\ell_1)\frac1{G^2\Omega^6}\right),
\qquad
\frac{\Delta^3}{H}\frac1{G^2\Omega^6}\ll T\ll \frac{\Delta^3}{H}\frac{GU^{15}}{\Omega^6}.
\]
Lemma 4.2 now gives, for each fixed \(f\),
\[
\sum_{r\asymp R}1_{\|\varphi_f(r)\|\ll \delta}
\ll R\delta+R\sqrt{\delta/T}+T+1.
\]
Using the lower and upper bounds on \(T\), and \(R\asymp HG\Omega^3/\Delta\), we obtain
\[
R\delta\ll \frac{H}{\Delta}\frac{\Delta^2}{H}\frac{G^2U^{20}}{\Omega^3},
\]
\[
R\sqrt{\delta/T}
\ll \frac{H}{\Delta}\frac{1}{\Delta^{1/2}}G^{5/2}U^{10}\Omega^3,
\]
\[
T+1\ll \frac{H}{\Delta}\left(\frac{\Delta^2}{H}\frac{G^2U^{20}}{\Omega^3}
+\frac{1}{\Delta^{1/2}}G^{5/2}U^{10}\Omega^3\right),
\]
where the last line uses \(H/\Delta^2\gg GU^{10}\) to absorb the \(T\)-term and the constant. The number of admissible integers \(f\) is
\[
O\!\left(G^2U^5\Omega\frac{HV_+}{\Delta^3}+1\right)
=O\!\left(G^2U^5\Omega\frac{HV_+}{\Delta^3}\right),
\]
because \(V_+\gg \Delta^3/H\). Multiplying the bound for one fixed \(f\) by this quantity gives
\[
\#\{r\in \mathcal R_a(\ell_1,\ell_2):0<|v(r)|\le V_+\}
\ll \frac{H}{\Delta}
\left(\frac{\Delta^2}{H}\frac{G^4U^{35}}{\Omega^8}
+\frac{G^{9/2}U^{25}}{\Delta^{1/2}\Omega^2}\right)
\frac{HV_+}{\Delta^3}.
\]

**Step 3: the monotone part of the small-defect range.**
Suppose now that
\[
C\frac{\Delta^3}{H}\frac{U^{10}}{\Omega^6}\le |v(r)|\le V_+
\qquad\text{and}\qquad
V_+\ll \frac{\Delta U^5}{\Omega^3},
\]
with \(C\) sufficiently large. Then the \(v\)-term dominates in \(\mathcal Q\), so
\[
|\mathcal Q|\asymp \ell_1G\Omega\frac{H|v|}{\Delta^3}.
\]
Restrict to a dyadic subrange \(|v|\asymp V\). For the corresponding integers \(f\), one has
\[
|f|\asymp \ell_1G\Omega\frac{HV}{\Delta^3}.
\]
In this regime the two monomials inside \(\varphi_f\) have different sizes, so for \(C\) sufficiently large
\[
|\varphi_f'(\rho)|\asymp \frac{T}{R},
\qquad
T:=\frac{D^4}{Xa}|f|,
\qquad
\frac{\Delta^3}{H}\ll T\ll GU^5\frac{HV}{\Delta^2\Omega}.
\]
Since \(T\gg \delta\), Lemma 4.1 gives for each such \(f\)
\[
\sum_{r\asymp R}1_{\|\varphi_f(r)\|\ll \delta}
\ll R\delta+T+1
\ll \frac{H}{\Delta}\frac{\Delta^2}{H}\frac{G^3U^{15}}{\Omega^3}.
\]
The number of admissible \(f\) with \(|f|\asymp \ell_1G\Omega HV/\Delta^3\) is \(O(\ell_1G\Omega HV/\Delta^3)\), so the contribution of \(|v|\asymp V\) is
\[
\ll \frac{H}{\Delta}\frac{\Delta^2}{H}\frac{G^3U^{15}}{\Omega^3}\cdot \ell_1G\Omega\frac{HV}{\Delta^3}
\ll \frac{HV}{\Delta^2}\frac{G^5U^{20}}{\Omega^2}.
\]
Summing dyadically over \(V\le V_+\) yields
\[
\#\left\{r\in \mathcal R_a(\ell_1,\ell_2):C\frac{\Delta^3}{H}\frac{U^{10}}{\Omega^6}\le |v(r)|\le V_+\right\}
\ll \frac{HV_+}{\Delta^2}\frac{G^5U^{20}}{\Omega^2}.
\]

**Step 4: the large-defect range.**
Define
\[
\Upsilon:=\ell_2^2(\ell_2-\ell_1)^2\widehat S_{a,\ell_1b_0}(d)
-\ell_1^2(\ell_2-\ell_1)^2\widehat S_{a,\ell_2b_0+v}(d)
+\ell_1^2\ell_2^2\widehat S_{a,(\ell_2-\ell_1)b_0+v}(d+\ell_1b_0).
\]
Because \(\widehat S_{a,b}(d)\in \mathbf Z+O(1/\Delta)\) on \(\mathcal D_a\), one has
\[
\Upsilon\in \mathbf Z+O\!\left(\frac{W^4}{\Delta}\right).
\]
To expand \(\Upsilon\), first note that
\[
\frac{X}{(d+\ell_1b_0)^5}=\frac{X}{d^5}\left(1-5\frac{\ell_1b_0}{d}+O\!\left(\frac{W^2b_0^2}{d^2}\right)\right),
\]
and for the relevant values of \(b\) one has
\[
\frac{Xab^5}{d^7}\ll \frac{\Delta^4}{H^2}\frac{GU^{25}}{\Omega^{14}}.
\]
Substituting the truncated expansion for \(\widehat S_{a,b}\), and collecting the cubic and quartic combinations, gives
\[
\Upsilon=\frac{Xa}{d^5}\left(\left(-4+\frac{10a}{d}\right)\left(p_1(v)+\frac{p_2(v)}{d}\right)\right)+O\!\left(\frac{\Delta^4}{H^2}\frac{G^5U^{45}}{\Omega^{14}}\right),
\]
where
\[
p_1(v)=3\ell_1^3\ell_2(\ell_2-\ell_1)b_0v^2+\ell_1^3(2\ell_2-\ell_1)v^3,
\]
\[
p_2(v)=-5\ell_1^3\ell_2^2(\ell_2-\ell_1)^2b_0^3v
-15\ell_1^3\ell_2^2(\ell_2-\ell_1)b_0^2v^2
-5\ell_1^3\ell_2(3\ell_2-2\ell_1)b_0v^3
-\frac52\ell_1^3(2\ell_2-\ell_1)v^4.
\]
Assume now that
\[
|v|\ge C\left(\frac{\Delta^3}{H}\frac{G^{5/2}U^{45/2}}{\Omega^6}+\Delta^{1/2}G^2U^{10}\Omega\right)
\]
with \(C\) sufficiently large. Since \(b_0\asymp B\), this lower bound implies
\[
\frac{|p_1(v)|}{|p_2(v)|/d}\gg C,
\]
so the \(p_1\)-term dominates \(p_2/d\). It also dominates both the expansion error and the \(W^4/\Delta\)-error coming from the fact that \(\Upsilon\) is only near an integer. Therefore there exists a nonzero integer
\[
1\le |s|\ll G^5U^{35}\Omega^{-8}
\]
such that
\[
\frac{Xa}{\widetilde d_a(r)^5}\left(-4+\frac{10a}{\widetilde d_a(r)}\right)
\left(\widetilde p_1(v,r)+\frac{\widetilde p_2(v,r)}{\widetilde d_a(r)}\right)
=
s+O\!\left(\frac{\Delta^4}{H^2}\frac{G^5U^{45}}{\Omega^{14}}+\frac{G^4U^{20}}{\Delta}\right),
\]
where \(\widetilde p_i(v,r)\) is obtained from \(p_i(v)\) by replacing \(b_0\) with \(\widetilde b_a(r)\).
Let
\[
\Sigma_s(r):=\frac{Xa}{\widetilde d_a(r)^5}\left(-4+\frac{10a}{\widetilde d_a(r)}\right)
\left(\widetilde p_1(v,r)+\frac{\widetilde p_2(v,r)}{\widetilde d_a(r)}\right).
\]
In the present range, \(\widetilde p_1\) still dominates \(\widetilde p_2/\widetilde d_a\), so
\[
|\Sigma_s^{(j)}(\rho)|\asymp \frac{|s|}{R^j}
\qquad (j=0,1,2).
\]
The mean value theorem now shows that, for each fixed nonzero \(s\) and admissible \(v\), the relevant \(r\)-values lie in an interval \(I_s(v)\) of length
\[
|I_s(v)|\ll R\left(\frac{\Delta^4}{H^2}\frac{G^5U^{45}}{\Omega^{14}}+\frac{G^4U^{20}}{\Delta}\right)
\ll \frac{H}{\Delta}\left(\frac{\Delta^4}{H^2}\frac{G^6U^{45}}{\Omega^{11}}+\frac{G^5U^{20}\Omega^3}{\Delta}\right).
\]
Moreover, solving the main term \(\Sigma_s(r)\asymp s\) for \(v\) gives the scale
\[
|v|\asymp V_s:=\left(\frac{D^5|s|}{XAB\ell_1^3\ell_2(\ell_2-\ell_1)}\right)^{1/2}.
\]
For fixed \(s\), there are therefore only \(O(1+\ell_1V_s)\) admissible values of \(v\in \ell_1^{-1}\mathbf Z\) with \(|v|\asymp V_s\).
On each \(I_s(v)\), consider
\[
\varphi_v(r):=6\ell_1\frac{Xav}{\widetilde d_a(r)^4}-12\ell_1\ell_2(\ell_2-\ell_1)\frac{Xa\widetilde b_a(r)^2}{\widetilde d_a(r)^5}.
\]
The earlier expansion of \(\mathcal Q\) gives
\[
\varphi_v(r)=\mathcal Q+O\!\left(\frac1\Delta\frac{G^4U^{15}}{\Omega^5}\right).
\]
Also,
\[
|\varphi_v'(\rho)|\asymp \frac{T}{R},
\qquad
T:=\ell_1\frac{XAV_s}{D^4},
\qquad
\frac{\delta}{T/R}\gg 1,
\]
where
\[
\delta:=\frac1\Delta\frac{G^4U^{15}}{\Omega^5}.
\]
Applying Lemma 4.1 on each interval \(I_s(v)\) yields
\[
\#\{r\in I_s(v):\|\varphi_v(r)\|\ll \delta\}
\ll |I_s(v)|\,\delta+\frac{\delta}{T/R}.
\]
Hence the total contribution of the present large-defect range is bounded by
\[
\sum_{1\le |s|\ll \ell_1^3\ell_2(\ell_2-\ell_1)U^{10}/\Omega^8}
(1+\ell_1V_s)\left(|I_s(v)|\,\delta+\frac{\delta}{T/R}\right).
\]
Write
\[
S:=\ell_1^3\ell_2(\ell_2-\ell_1)\frac{U^{10}}{\Omega^8}.
\]
Then the \(s\)-sum in the previous display is over \(1\le |s|\ll S\), and
\[
\sum_{1\le |s|\ll S}1\ll S,
\qquad
\sum_{1\le |s|\ll S}|s|^{1/2}\ll S^{3/2},
\qquad
\sum_{1\le |s|\ll S}|s|^{-1/2}\ll S^{1/2}.
\]
Also, from the definition of \(V_s\) and the identity \(D^5/(XaB)=\Delta^2\Omega^2\),
\[
V_s=\Delta\Omega\left(\frac{|s|}{\ell_1^3\ell_2(\ell_2-\ell_1)}\right)^{1/2},
\qquad
\ell_1V_s=\Delta\Omega\left(\frac{|s|}{\ell_1\ell_2(\ell_2-\ell_1)}\right)^{1/2}.
\]
Likewise,
\[
\frac{T}{R}\asymp \frac{1}{\Delta\Omega}
\left(\frac{|s|}{\ell_1\ell_2(\ell_2-\ell_1)}\right)^{1/2},
\qquad
\frac{\delta}{T/R}\asymp \frac{G^4U^{15}}{\Omega^4}
\left(\frac{\ell_1\ell_2(\ell_2-\ell_1)}{|s|}\right)^{1/2}.
\]
Finally,
\[
|I_s(v)|\,\delta
\ll
\frac{H}{\Delta}\left(
\frac{\Delta^2}{H}\frac{G^{10}U^{60}}{\Omega^{16}}
+\frac{1}{\Delta}\frac{G^9U^{35}}{\Omega^2}
\right).
\]
The contribution of the second summand here, multiplied by \(\ell_1V_s\), is therefore
\[
\ll
\frac{H}{\Delta}\frac{1}{\Delta}\frac{G^9U^{35}}{\Omega^2}
\cdot \Delta\Omega\frac{S^{3/2}}{(\ell_1\ell_2(\ell_2-\ell_1))^{1/2}}
\ll
\frac{H}{\Delta}\frac{1}{\Delta}\ell_1^4\ell_2(\ell_2-\ell_1)\frac{G^9U^{50}}{\Omega^{13}}.
\]
The analogous computation with the first summand of \(|I_s(v)|\,\delta\) gives
\[
\ll
\frac{H}{\Delta}\frac{\Delta^2}{H}\ell_1^4\ell_2(\ell_2-\ell_1)\frac{G^9U^{65}}{\Omega^{27}}.
\]
The four remaining combinations, namely the contribution of the term \(1\) in \(1+\ell_1V_s\) and the contribution of \(\delta/(T/R)\), are smaller after using the displayed bounds for \(S\), together with \(\Omega\ll U\) and \(\Omega\gg G^{-1/4}U^{-3/4}\). Hence
\[
\ll \frac{H}{\Delta}\left(\frac{1}{\Delta}\ell_1^4\ell_2(\ell_2-\ell_1)\frac{G^9U^{50}}{\Omega^{13}}
+\frac{\Delta^2}{H}\ell_1^4\ell_2(\ell_2-\ell_1)\frac{G^9U^{65}}{\Omega^{27}}\right).
\]
Since \(\ell_1,\ell_2\ll W\asymp GU^5\), this is
\[
\ll \frac{H}{\Delta}\left(\frac{G^{14}U^{75}}{\Delta\Omega^{13}}+\frac{\Delta^2}{H}\frac{G^{14}U^{90}}{\Omega^{27}}\right).
\]
Therefore
\[
\#\left\{r\in \mathcal R_a(\ell_1,\ell_2):|v(r)|\ge C\left(\frac{\Delta^3}{H}\frac{G^{5/2}U^{45/2}}{\Omega^6}+\Delta^{1/2}G^2U^{10}\Omega\right)\right\}
\ll \frac{H}{\Delta}\left(\frac{G^{14}U^{75}}{\Delta\Omega^{13}}+\frac{\Delta^2}{H}\frac{G^{14}U^{90}}{\Omega^{27}}\right).
\]

**Step 5: combine the three ranges.**
Take \(V_1\) to be a sufficiently large multiple of
\[
\frac{\Delta^3}{H}\frac{U^{10}}{\Omega^6},
\]
and \(V_2\) to be a sufficiently large multiple of
\[
\frac{\Delta^3}{H}\frac{G^{5/2}U^{45/2}}{\Omega^6}+\Delta^{1/2}G^2U^{10}\Omega.
\]
Applying the zero-defect bound, the general small-defect bound with \(V_+=V_1\), the monotone small-defect bound with \(V_+=V_2\), and the large-defect bound, we find that \(\#\mathcal R_a(\ell_1,\ell_2)\) is
\[
\ll \frac{H}{\Delta}\Biggl(
\frac{1}{\Delta}\frac{G^4U^{10}}{\Omega^2}
+\frac{\Delta^2}{H}\frac{G^4U^{45}}{\Omega^{14}}
+\frac{1}{\Delta^{1/2}}\frac{G^{9/2}U^{35}}{\Omega^8}
+\frac{\Delta^2}{H}\frac{G^{15/2}U^{85/2}}{\Omega^8}
+\frac{1}{\Delta^{1/2}}\frac{G^7U^{30}}{\Omega}
+\frac{1}{\Delta}\frac{G^{14}U^{75}}{\Omega^{13}}
+\frac{\Delta^2}{H}\frac{G^{14}U^{90}}{\Omega^{27}}
\Biggr).
\]
We now simplify these seven terms explicitly. First,
\[
\frac{1}{\Delta}\frac{G^4U^{10}}{\Omega^2}
\le
\frac{1}{\Delta^{1/2}}\frac{G^7U^{41}}{\Omega},
\]
because \(\Delta\gg G^2U^5\) and \(\Omega\le U\). Also,
\[
\frac{1}{\Delta^{1/2}}\frac{G^{9/2}U^{35}}{\Omega^8}
\le
\frac{1}{\Delta^{1/2}}\frac{G^{9/2}U^{35}}{\Omega}
\left(G^{1/4}U^{3/4}\right)^7
\le
\frac{1}{\Delta^{1/2}}\frac{G^7U^{41}}{\Omega},
\]
using \(\Omega\gg G^{-1/4}U^{-3/4}\). The fifth term is itself bounded by
\[
\frac{1}{\Delta^{1/2}}\frac{G^7U^{41}}{\Omega}.
\]
Next,
\[
\frac{\Delta^2}{H}\frac{G^4U^{45}}{\Omega^{14}}
\le
\frac{\Delta^2}{H}\frac{G^{14}U^{90}}{\Omega^{27}},
\qquad
\frac{\Delta^2}{H}\frac{G^{15/2}U^{85/2}}{\Omega^8}
\le
\frac{\Delta^2}{H}\frac{G^{14}U^{90}}{\Omega^{27}},
\]
because \(G,U\ge 1\) and \(\Omega\le U\). Thus
\[
\#\mathcal R_a(\ell_1,\ell_2)
\ll \frac{H}{\Delta}\left(
\frac{1}{\Delta^{1/2}}\frac{G^7U^{41}}{\Omega}
+\frac{1}{\Delta}\frac{G^{14}U^{75}}{\Omega^{13}}
+\frac{\Delta^2}{H}\frac{G^{14}U^{90}}{\Omega^{27}}
\right).
\]
Finally, summing over the \(O(W^2)\asymp G^2U^{10}\) possible pairs \((\ell_1,\ell_2)\) gives
\[
\#\mathcal R_a\ll \frac{H}{\Delta}\left(
\frac{G^9U^{51}}{\Delta^{1/2}\Omega}
+\frac{G^{17}U^{85}}{\Delta\Omega^{13}}
+\frac{\Delta^2}{H}\frac{G^{17}U^{100}}{\Omega^{27}}
\right).
\]
This is the desired bound. ∎
---

## 6. The range \(\Delta\gtrsim H^{1/2}\)

### Proposition 6.1
For \(\Omega=A/\Delta\),
\[
\sum_{a\sim A}\#\mathcal R_a
\ll
HX^{O(u)}\left(\frac{H}{\Delta^2}G\Omega^2+\left(\frac{H}{\Delta^2}\right)^{2/3}G^{4/3}\Omega^{11/3}+\frac{G^{1/2}\Omega^{5/2}}{H^{1/2}}\right).
\]

#### Proof
For \(r\in \mathcal R_a\), let
\[
f_a^*(r):=\text{the nearest integer to }F_a(d_a^*(r)),
\qquad
\widetilde f_a(r):=F_a(\widetilde d_a(r)).
\]
By the approximation of \(d_a^*(r)\) and the Taylor expansion of \(F_a\),
\[
\widetilde f_a(r)=f_a^*(r)+O\!\left(\frac{H}{\Delta^2\Omega^2}\right).
\]
Hence
\[
\#\mathcal R_a\ll \sum_{r\asymp R}1_{\|\widetilde f_a(r)\|\ll H/(\Delta^2\Omega^2)}.
\]
Now, as a function of \(a\) with \(r\) fixed, one has
\[
|\widetilde f_a(r)|,\ A\left|\frac{\partial}{\partial a}\widetilde f_a(r)\right|,\ A^2\left|\frac{\partial^2}{\partial a^2}\widetilde f_a(r)\right|\asymp F
\]
where
\[
F:=\frac{H^2}{\Delta^2}G\Omega=HxG\Omega.
\]
Applying Proposition 4.3 in the variable \(a\), with
\[
N=A,\qquad T=F,\qquad \delta=\frac{H}{\Delta^2\Omega^2}=\frac{x}{\Omega^2},
\]
gives
\[
\sum_{a\sim A}1_{\|\widetilde f_a(r)\|\ll H/(\Delta^2\Omega^2)}
\ll
A\delta+(AF)^{1/3}+A\sqrt{\frac{\delta}{F}}\log\!\left(2+A\sqrt{\frac{\delta}{F}}\right)+1.
\]
Since
\[
A\delta=\frac{AH}{\Delta^2\Omega^2}=\frac{H}{A},
\qquad
A\sqrt{\frac{\delta}{F}}=\frac{A}{\sqrt{FA^2/H}},
\]
this is the displayed bound. Also
\[
AF=\Delta\Omega\cdot HxG\Omega=H^{3/2}x^{1/2}G\Omega^2\gg 1,
\]
so the \(+1\)-term is absorbed into \((AF)^{1/3}\). Moreover,
\[
\frac{A}{\sqrt{FA^2/H}}=x^{-1/2}G^{-1/2}\Omega^{-1/2}\ll X,
\]
so the logarithm contributes only a factor \(X^{O(u)}\).
Multiplying the three main terms by \(R\asymp HG\Omega^3/\Delta\) gives
\[
R\cdot \frac{H}{A}
\asymp \frac{HG\Omega^3}{\Delta}\cdot \frac{H}{\Delta\Omega}
=HxG\Omega^2,
\]
\[
R(AF)^{1/3}
\asymp \frac{HG\Omega^3}{\Delta}\cdot (\Delta\Omega\cdot HxG\Omega)^{1/3}
=Hx^{2/3}G^{4/3}\Omega^{11/3},
\]
\[
R\cdot \frac{A}{\sqrt{FA^2/H}}
\asymp \frac{HG\Omega^3}{\Delta}\cdot x^{-1/2}G^{-1/2}\Omega^{-1/2}
=H^{1/2}G^{1/2}\Omega^{5/2}.
\]
Factoring out \(H\) gives exactly
\[
\sum_{a\sim A}\#\mathcal R_a
\ll
HX^{O(u)}\left(xG\Omega^2+x^{2/3}G^{4/3}\Omega^{11/3}+H^{-1/2}G^{1/2}\Omega^{5/2}\right),
\]
which is the stated bound. ∎

---

## 7. The final direct small-value argument


Fix \(a\sim A\) and write
\[
\widetilde f_a(r)=F_a(\widetilde d_a(r)).
\]
Set
\[
F:=\frac{H^2}{\Delta^2}G\Omega.
\]
For each integer \(j\) with
\[
|j|\ll 1+\frac{H}{A^2},
\]
define
\[
g_j(r):=\breve d_a(\widetilde f_a(r)+j)-\breve d_a'(\widetilde f_a(r)+j)\{\widetilde f_a(r)\},
\]
where \(\breve d_a:=F_a^{-1}\). Since
\[
F_a(d_a^*(r))\in \mathbf Z+O\!\left(\frac{1}{H\Delta^2}\right),
\]
there exists such a \(j\) with
\[
f_a^*(r)=\lfloor \widetilde f_a(r)\rfloor+j.
\]
Using
\[
d_a^*(r)=\breve d_a(f_a^*(r))+O\!\left(\frac{\Delta^2}{H^2GA}\right)
\]
and the inverse-function scale
\[
F\,\breve d_a'(t)\asymp H\Delta,\qquad F^2\,\breve d_a''(t)\asymp H\Delta
\qquad (t\asymp F),
\]
we may Taylor expand \(\breve d_a\) at \(\widetilde f_a(r)+j\):
\[
\breve d_a(f_a^*(r))
=
\breve d_a(\widetilde f_a(r)+j-\{\widetilde f_a(r)\})
\]
\[
=
\breve d_a(\widetilde f_a(r)+j)
-\breve d_a'(\widetilde f_a(r)+j)\{\widetilde f_a(r)\}
+O\!\left(\sup_{t\asymp F}|\breve d_a''(t)|\right).
\]
Since \(\sup_{t\asymp F}|\breve d_a''(t)|\asymp H\Delta/F^2\), and
\[
\frac{H\Delta}{F^2}
=
\frac{H\Delta}{(H^2\Delta^{-2}G\Omega)^2}
=
\frac{\Delta^5}{H^3G^2\Omega^2}
=
\frac{\Delta^5}{H^3}\Bigl(\frac{\Delta}{A}\Bigr)^2,
\]
we obtain
\[
\#\mathcal R_a\le \sum_{|j|\ll 1+H/A^2}\ \sum_{r\asymp R}1_{\|g_j(r)\|\le \delta_0},
\]
with
\[
\delta_0:=\frac{\Delta^5}{H^3}\Bigl(\frac{\Delta}{A}\Bigr)^2+\frac{\Delta^2}{H^2GA}.
\]

Write
\[
x:=\frac{H}{\Delta^2}.
\]
Then
\[
R=\frac{HG\Omega^3}{\Delta}=H^{1/2}x^{1/2}G\Omega^3,
\]
and the scale parameters are
\[
T_1:=\frac{H\Delta}{F}=H^{1/2}x^{-3/2}(G\Omega)^{-1},
\]
\[
T_2:=F=HxG\Omega,
\]
\[
T_3:=H\Delta=H^{3/2}x^{-1/2}.
\]
Thus
\[
\frac{T_1}{R}=x^{-2}G^{-2}\Omega^{-4},\qquad
\frac{T_2}{R^2}=G^{-1}\Omega^{-5},\qquad
\frac{T_3}{R^3}=G^{-3}\Omega^{-9}x^{-2}.
\]

### Proposition 7.1
For each fixed \(j\),
\[
\#\{r\asymp R:\|g_j(r)\|\le \delta_0\}\ll \frac{R}{W},
\]
provided
\[
W\le c\min\!\left(
H^{1/16}x^{5/16}\Omega^{1/4},
\ H^{1/28}x^{5/28}G^{1/14}\Omega^{1/2},
\ H^{1/40}x^{1/8}G^{1/5}\Omega^{3/5},
\ H^{1/18}x^{1/18}G^{-1/3}\Omega^{-7/9},
\ H^{1/42}x^{1/42}G^{-1/21}\Omega^{1/7},
\ H^{1/30}x^{1/30}\Omega^{-2/15},
\ H^{1/54}x^{1/54}G^{2/27}\Omega^{8/27},
\ H^{1/30}x^{1/6}G^{4/15}\Omega^{4/5},
\ H^{1/42}x^{5/42}G^{5/21}\Omega^{17/21},
\ H^{1/48}x^{5/48}G^{1/8}\Omega^{7/24},
\ H^{1/16}x^{1/16}G^{-1/16}\Omega^{1/16},
\ H^{1/22}x^{1/22}G^{1/11}\Omega^{3/11},
\ H^{1/16}x^{1/16}G^{1/8}\Omega^{3/8},
\ H^{1/84}x^{5/84}G^{1/7}\Omega^{11/21},
\ H^{1/28}x^{1/28}G^{1/28}\Omega^{11/28},
\ H^{1/34}x^{1/34}G^{2/17}\Omega^{8/17},
\ H^{1/28}x^{1/28}G^{1/7}\Omega^{4/7},
\ H^{1/16}x^{-1/16},
\ H^{1/28}x^{-1/28}G^{1/14}\Omega^{5/14},
\ H^{1/24}x^{5/24}G^{1/4}\Omega^{7/12},
\ H^{1/36}x^{5/36}G^{2/9}\Omega^{2/3}
\right)
\]
for a sufficiently small absolute constant \(c>0\).

Equivalently, the Lean-facing Section 7 hypothesis is the bundled full
admissibility envelope consisting of:
the original nine integer-power constraints, the four no-absorption residual
constraints
\[
W^{16}\le H^3xG^2\Omega^2,\qquad
W^{28}\le H^3xG^4\Omega^{12},
\]
\[
W^{18}x^3G^4\Omega^{16}\le H^3,\qquad
W^{42}x^3\le H^3\Omega^4,
\]
the two offset constraints
\[
W^{12}\ll H^{1/2}x^{5/2}G^3\Omega^7,
\qquad
W^{18}\ll H^{1/2}x^{5/2}G^4\Omega^{12},
\]
the ten nonzero-top-carry constraints displayed above, equivalently the eight
main nonzero-top-carry constraints together with the two residual square-root
constraints
\[
W^{16}x\ll H,\qquad W^{28}x\ll HG^2\Omega^{10},
\]
and the Section 4.3
side conditions
\[
R>1,\qquad T_1>1,\qquad 0<\delta_1(h)<1,\qquad |F''|\asymp1.
\]
The old nine-constraint predicate remains useful only for legacy routes; the
final Section 7 route uses this full envelope.

#### Proof
Fix \(j\) and set
\[
E:=\{r\asymp R:\|g_j(r)\|\le \delta_0\}.
\]
Assume
\[
M:=\#E>\frac{R}{W}.
\]

### Lemma 7.2 (averaged popular cube)
For integer shifts \(1\le h_1\le \lfloor W\rfloor\),
\(1\le h_2\le \lfloor W^2\rfloor\), and
\(1\le h_3\le \lfloor W^4\rfloor\), set
\[
E_3(h_1,h_2,h_3)
:=\{r:r+\varepsilon_1h_1+\varepsilon_2h_2+\varepsilon_3h_3\in E
\text{ for all }\varepsilon_i\in\{0,1\}\}.
\]
Then
\[
\sum_{1\le h_1\le W}
\sum_{1\le h_2\le W^2}
\sum_{1\le h_3\le W^4}
|E_3(h_1,h_2,h_3)|
\gg \frac{R}{W}.
\]

#### Proof
This is the averaged form of the threefold Lemma 2.2 differencing argument.
The Lean statement used for Section 7 is `BracketAveragedCubeLowerBound`, with
shift lengths \(\lfloor W\rfloor,\lfloor W^2\rfloor,\lfloor W^4\rfloor\).
It gives the displayed lower bound for the total number of eight-corner cubes
in the whole rectangular shift box.  No lower bound on any individual product
\(h_1h_2h_3\) is used. ∎

Fix one triple \((h_1,h_2,h_3)\) in the rectangular shift box and let
\[
P:=h_1h_2h_3,\qquad
S:=h_1h_2+h_1h_3+h_2h_3.
\]
Thus \(P\ll W^7\) and \(S\ll W^6\).  For \(r\in E_3(h_1,h_2,h_3)\),
\[
\|\Delta_{h_1,h_2,h_3}g_j(r)\|\le 8\delta_0.
\]

Now write
\[
g_j(r)=f_3(r)+f_1(r)\{f_2(r)\},
\]
where
\[
f_3(r):=\breve d_a(\widetilde f_a(r)+j),\qquad
f_1(r):=-\breve d_a'(\widetilde f_a(r)+j),\qquad
f_2(r):=\widetilde f_a(r).
\]
Then
\[
f_1^{(m)}(r)\asymp \frac{T_1}{R^m},\qquad
f_2^{(m)}(r)\asymp \frac{T_2}{R^m},\qquad
f_3^{(m)}(r)\asymp \frac{T_3}{R^m}.
\]

We now keep the integer carries explicitly.  The product rule for the
third difference gives
\[
\Delta_{h_1,h_2,h_3}(f_1\{f_2\})(r)
=
f_1(r+h_\Sigma)\Delta_{h_1,h_2,h_3}\{f_2\}(r)
+\sum_{i=1}^3
\Delta_{h_i}f_1(r+h_\Sigma-h_i)
\Delta_{h_j,h_k}\{f_2\}(r+\xi_i)
+O\!\left(\frac{ST_1}{R^2}\right),
\tag{7.1}
\]
where \(h_\Sigma=h_1+h_2+h_3\), \(\{i,j,k\}=\{1,2,3\}\), and the shifts
\(\xi_i\) are bounded by \(h_\Sigma\).  The error term contains all terms
with at least two differences falling on \(f_1\).  Its size follows from
\(f_1^{(m)}(r)\ll T_1/R^m\) and is
\[
O\!\left(\frac{ST_1}{R^2}\right).
\]

Set
\[
B_{03}(r):=\Delta_{h_1,h_2,h_3}f_2(r),
\]
\[
B_1(r):=\Delta_{h_2,h_3}f_2(r+\xi_1),\quad
B_2(r):=\Delta_{h_1,h_3}f_2(r+\xi_2),\quad
B_3(r):=\Delta_{h_1,h_2}f_2(r+\xi_3).
\]
After fixing one of the finitely many floor-carry branches, there are fixed
integers \(\rho_0,\rho_1,\rho_2,\rho_3=O(1)\) such that
\[
\Delta_{h_1,h_2,h_3}\{f_2\}(r)=B_{03}(r)+\rho_0
\]
and, after also fixing \(u_i=\lfloor B_i(r)\rfloor\),
\[
\Delta_{h_j,h_k}\{f_2\}(r+\xi_i)=B_i(r)-u_i+\rho_i.
\]
The triple \(\mathbf u=(u_1,u_2,u_3)\) takes only
\[
O\!\left(1+\frac{ST_2}{R^2}\right)
=O\!\left(1+\frac{S}{G\Omega^5}\right)
\tag{7.2}
\]
values, because
\[
B_i(r)=h_jh_k f_2''(r)+O\!\left(\frac{PT_2}{R^3}\right),
\qquad
f_2''(r)\asymp \frac{T_2}{R^2}=G^{-1}\Omega^{-5}.
\]
The carry/fiber cover supplied by the floor-branching lemma represents each
fixed branch and fixed \(\mathbf u\) by \(O(1)\) intervals in \(r\) on which
the integer data are fixed.  The point-near-curve estimates below are applied
on one such interval at a time, and this \(O(1)\) interval count is absorbed
in the factor (7.2).

Thus, on a fixed carry branch and a fixed fiber \(\mathbf u\),
\[
\|\Phi_{\rho,\mathbf u}(r)\|\ll
\delta_1(h):=\delta_0+\frac{ST_1}{R^2}
=\delta_0+\frac{S}{Rx^2G^2\Omega^4},
\tag{7.3}
\]
where
\[
\Phi_{\rho,\mathbf u}(r)
:=\Delta_{h_1,h_2,h_3}f_3(r)
+f_1(r+h_\Sigma)(B_{03}(r)+\rho_0)
+\sum_{i=1}^3
\Delta_{h_i}f_1(r+h_\Sigma-h_i)(B_i(r)-u_i+\rho_i).
\tag{7.4}
\]

The asymptotic expansions of \(R_a(d)\) and \(F_a(d)\) imply
\[
\widetilde d_a(r)=c_d\,D\,(r/R)^{-1/4}\bigl(1+O(a/\widetilde d_a(r))\bigr),
\]
\[
f_2(r)=c_2\,T_2\,(r/R)^{3/4}\bigl(1+O(a/\widetilde d_a(r))\bigr),
\]
\[
f_1(r)=c_1\,T_1\,(r/R)^{-1}\bigl(1+O(a/\widetilde d_a(r))\bigr),
\]
\[
f_3(r)=c_3\,T_3\,(r/R)^{-1/4}\bigl(1+O(a/\widetilde d_a(r))\bigr),
\]
with \(c_d,c_1,c_2,c_3\neq 0\) and
\[
a/\widetilde d_a(r)\ll \frac{A}{D}=\frac{\Omega}{H}=X^{-(1-g)/5+O(u)}=o(1).
\]
Differencing the leading monomials gives, with \(y=r/R\),
\[
f_1(r+h_\Sigma)
=c_1T_1y^{-1}-c_1h_\Sigma\frac{T_1}{R}y^{-2}
+O\!\left(h_\Sigma^2\frac{T_1}{R^2}+T_1X^{-(1-g)/5+O(u)}\right),
\]
\[
\Delta_{h_i}f_1(r+h_\Sigma-h_i)
=-c_1h_i\frac{T_1}{R}y^{-2}
+O\!\left(h_ih_\Sigma\frac{T_1}{R^2}+h_i\frac{T_1}{R}X^{-(1-g)/5+O(u)}\right),
\]
\[
B_i(r)=\beta_i h_jh_k\frac{T_2}{R^2}y^{-5/4}
+O\!\left(h_jh_k\frac{T_2}{R^2}X^{-(1-g)/5+O(u)}
+h_jh_kh_\Sigma\frac{T_2}{R^3}\right),
\]
\[
B_{03}(r)=\beta_0P\frac{T_2}{R^3}y^{-9/4}
+O\!\left(P\frac{T_2}{R^3}X^{-(1-g)/5+O(u)}
+Ph_\Sigma\frac{T_2}{R^4}\right),
\]
and
\[
\Delta_{h_1,h_2,h_3}f_3(r)
=\gamma_0P\frac{T_3}{R^3}y^{-13/4}
+O\!\left(P\frac{T_3}{R^3}X^{-(1-g)/5+O(u)}
+Ph_\Sigma\frac{T_3}{R^4}\right).
\]
Since \(T_1T_2/R^3=T_3/R^3\), the leading part of
\(\Phi_{\rho,\mathbf u}\) is
\[
\Phi_{\rho,\mathbf u}(r)
=c_1\rho_0T_1y^{-1}
+c_1\frac{T_1}{R}
\left(\sum_{i=1}^3h_i(u_i-\rho_i)-\rho_0h_\Sigma\right)y^{-2}
+C_*P\frac{T_3}{R^3}y^{-13/4}
+\operatorname{Err}(r),
\tag{7.5}
\]
where \(C_*\neq0\).  Indeed, the leading monomials give
\[
B_{03}(r)=\frac{15}{64}c_2P\frac{T_2}{R^3}y^{-9/4}+\cdots,
\]
so \(f_1(r+h_\Sigma)B_{03}(r)\) contributes
\(\frac{15}{64}c_1c_2P T_3R^{-3}y^{-13/4}\), while
\[
\sum_i\Delta_{h_i}f_1(r+h_\Sigma-h_i)B_i(r)
=\frac{9}{16}c_1c_2P\frac{T_3}{R^3}y^{-13/4}+\cdots,
\]
and
\[
\Delta_{h_1,h_2,h_3}f_3(r)
=-\frac{45}{64}c_3P\frac{T_3}{R^3}y^{-13/4}+\cdots.
\]
The inverse-function relation \(f_3'(r)=-f_1(r)f_2'(r)+O(T_3X^{-(1-g)/5+O(u)}/R)\)
implies \(c_3=3c_1c_2\).  Therefore
\[
C_*=-\frac{45}{64}c_3+\frac{51}{64}c_1c_2
=-\frac{21}{16}c_1c_2\neq0.
\]
Moreover
\[
\operatorname{Err}^{(m)}(r)
\ll
\frac{1}{R^m}
\left(
\mathbf 1_{\rho_0\ne0}T_1X^{-(1-g)/5+O(u)}
+
\left(h_\Sigma\frac{T_1}{R}+P\frac{T_3}{R^3}\right)X^{-(1-g)/5+O(u)}
+h_\Sigma^2\frac{T_1}{R^2}
\right).
\]
Here the terms of size \(Ph_\Sigma T_3/R^4\) from the Taylor remainders have
been absorbed into \(P(T_3/R^3)X^{-(1-g)/5+O(u)}\), since
\(h_\Sigma/R\le W^4/R\ll X^{-c}\) in the displayed \(W\)-range.
Thus in the branch \(\rho_0=0\) there is no stand-alone
\(T_1X^{-(1-g)/5+O(u)}\) error term.

We split according to whether the top carry \(\rho_0\) vanishes.

First suppose \(\rho_0=0\).  The \(T_1y^{-1}\)-term is absent.  The phase
has principal part
\[
B_{\rho,\mathbf u}y^{-2}+C_*P\frac{T_3}{R^3}y^{-13/4},
\qquad
|B_{\rho,\mathbf u}|
\ll h_\Sigma\frac{T_1}{R}+P\frac{T_3}{R^3}.
\]
The two monomials \(y^{-2}\) and \(y^{-13/4}\) have nonzero Wronskian, so
the principal parts of \(\Phi_{\rho,\mathbf u}'\) and
\(R\Phi_{\rho,\mathbf u}''\) cannot vanish simultaneously.  We use the actual
scale
\[
T_{\rho,\mathbf u}:=
|B_{\rho,\mathbf u}|+\left|C_*P\frac{T_3}{R^3}\right|.
\]
The Taylor remainder in (7.5) is subordinate to this scale.  The only
non-\(X^{-c}\) remainder is
\[
h_\Sigma^2\frac{T_1}{R^2}
\ll
P\frac{T_3}{R^3},
\]
because
\[
\frac{h_\Sigma^2T_1/R^2}{PT_3/R^3}
\ll
W^4\frac{\Omega^2}{(Hx)^{1/2}}
\ll X^{-c}
\]
for some \(c>0\), by the displayed \(W\)-constraints and the ambient bounds
\(x\gg GU^{10}\), \(\Omega\le U\), after shrinking \(u\) in terms of \(g\).
The \(X^{-c}\)-error involving the possibly larger coefficient
\(h_\Sigma T_1/R\) is also subordinate to the same lower scale, since
\[
\frac{h_\Sigma T_1R^{-1}}{P T_3R^{-3}}
\le
\frac{h_\Sigma}{P}G\Omega^5
\ll G\Omega^5
\]
and hence
\[
h_\Sigma\frac{T_1}{R}X^{-(1-g)/5+O(u)}
\ll
P\frac{T_3}{R^3}.
\]
It follows that, on each interval in the carry/fiber cover,
\[
|\Phi_{\rho,\mathbf u}'(r)|\ll \frac{T_{\rho,\mathbf u}}{R},
\qquad
|\Phi_{\rho,\mathbf u}'(r)|+R|\Phi_{\rho,\mathbf u}''(r)|
\asymp \frac{T_{\rho,\mathbf u}}{R},
\]
and \(\Phi_{\rho,\mathbf u}'\), \(\Phi_{\rho,\mathbf u}''\) each have \(O(1)\)
zeros.  Thus Lemma 4.2 applies with scale \(T_{\rho,\mathbf u}\).
Since \(C_*\neq0\),
\[
T_{\rho,\mathbf u}\gg P\frac{T_3}{R^3}
\asymp \frac{P}{x^2G^3\Omega^9},
\]
while
\[
T_{\rho,\mathbf u}
\ll
\frac{h_\Sigma}{x^2G^2\Omega^4}
+\frac{P}{x^2G^3\Omega^9}.
\]
For this fixed triple, using the lower bound for \(T_{\rho,\mathbf u}\) in the
square-root terms and the upper bound for the \(+T_{\rho,\mathbf u}\)-term,
Lemma 4.2 gives
\[
R\sqrt{\delta_0/T_{\rho,\mathbf u}}
\ll H^{1/4}x^{1/4}G^{5/2}\Omega^{13/2}P^{-1/2},
\]
\[
R\sqrt{\frac{S/(Rx^2G^2\Omega^4)}{T_{\rho,\mathbf u}}}
\ll H^{1/4}x^{1/4}G\Omega^4\left(\frac{S}{P}\right)^{1/2},
\]
and
\[
T_{\rho,\mathbf u}\ll
\frac{h_\Sigma}{x^2G^2\Omega^4}
+\frac{P}{x^2G^3\Omega^9}.
\]
Together with
\[
R\delta_1(h)\ll
\frac{G\Omega}{x^2}
+\frac{\Omega^2}{H}
+\frac{S}{x^2G^2\Omega^4},
\tag{7.6}
\]
the fiber count (7.2), and the offset contribution
\[
\left(1+\frac{S}{G\Omega^5}\right)\frac{h_\Sigma T_1}{R},
\]
we sum over the whole rectangular shift box.  The required elementary sums are
\[
\sum 1\ll W^7,\qquad \sum S\ll W^{13},\qquad \sum S^2\ll W^{19},
\]
\[
\sum P\ll W^{14},\qquad \sum SP\ll W^{20},
\]
\[
\sum P^{-1/2}\ll W^{7/2},\qquad
\sum SP^{-1/2}\ll W^{19/2},
\]
\[
\sum (S/P)^{1/2}\ll W^{13/2},\qquad
\sum S(S/P)^{1/2}\ll W^{25/2},
\]
\[
\sum h_\Sigma\ll W^{11},\qquad \sum Sh_\Sigma\ll W^{17},
\]
where all sums are over
\(1\le h_1\le \lfloor W\rfloor\),
\(1\le h_2\le \lfloor W^2\rfloor\), and
\(1\le h_3\le \lfloor W^4\rfloor\).
Comparing the resulting total upper bound with the averaged cube lower bound
\(\gg R/W\) gives the old nine constraints and the two extra offset constraints
\[
W^{12}\ll H^{1/2}x^{5/2}G^3\Omega^7,
\qquad
W^{18}\ll H^{1/2}x^{5/2}G^4\Omega^{12}.
\tag{7.7}
\]
The extra \(\Omega^2/H\) term in (7.6) is kept without absorption.  After
multiplication by the two fiber-complexity factors and comparison with
\(\gg R/W\), it gives the four no-absorption residual constraints
\[
W^{16}\le H^3xG^2\Omega^2,
\qquad
W^{28}\le H^3xG^4\Omega^{12},
\]
\[
W^{18}x^3G^4\Omega^{16}\le H^3,
\qquad
W^{42}x^3\le H^3\Omega^4.
\]
These are included explicitly in the final Section 7 admissibility envelope.

Now suppose \(\rho_0\ne0\).  Then the term \(c_1\rho_0T_1y^{-1}\) dominates
the principal part.  For the displayed choice of \(W\), the remaining monomials
in (7.5) are \(o(T_1)\).  Quantitatively this uses
\[
\frac{W^4}{R}\ll X^{-c},\qquad
\frac{P T_3}{R^3T_1}\ll X^{-c},\qquad
\frac{W^8}{R^2}\ll X^{-c}
\]
for some \(c>0\), after shrinking \(u\) in terms of \(g\).  These inequalities
are immediate from the displayed \(W\)-constraints, \(P\le W^7\), and the
ambient parameter range.  Thus the nonzero top-carry phase is treated by a
finite local version of Proposition 4.3, not by one global curvature
normalization on the whole dyadic interval.  Split each fixed grouped fiber
into absolutely many subintervals on which \(y=r/R\) ranges over an interval
where the leading factor \(y^{-3}\) varies by at most a fixed constant.  On
such a piece \(I_q\), choose a reference point \(y_q\asymp1\) and set
\[
T_{\rho,q}\asymp |\rho_0|\frac{a^2}{R}y_q^{-3}.
\]
Since \(a\asymp A=\Delta\Omega\) and
\[
R\asymp R_0:=H^{1/2}x^{1/2}G\Omega^3,\qquad
R_0T_1=A^2,
\]
we have, with absolute constants only,
\[
T_{\rho,q}\asymp |\rho_0|T_1\asymp T_1.
\]
The last comparison uses the fact that the coherent top-carry integer is
nonzero and is bounded by an absolute constant after the eight carry branches
are fixed.  The normalized phase on \(I_q\) is
\[
\Phi_{\rho,\mathbf u}(r)=T_{\rho,q}F_{\rho,\mathbf u,q}(r/R),
\]
and the preceding domination estimates give the literal local curvature
hypotheses
\[
1\le |F_{\rho,\mathbf u,q}''(y)|\le2
\]
on the inner interval of \(I_q\), after enlarging the fixed constants and
shrinking \(u\) in terms of \(g\).  The same bounds hold on the slightly wider
interval required by the local form of Proposition 4.3.

The remaining numerical hypotheses of Proposition 4.3 are the following
explicit side inequalities:
\[
R\ge W^8>1
\]
for every relevant dyadic window, and the base support scale is
\[
R_0=H^{1/2}x^{1/2}G\Omega^3,
\]
\[
T_1=H^{1/2}x^{-3/2}(G\Omega)^{-1}>1
\qquad\Longleftrightarrow\qquad
x^3G^2\Omega^2<H,
\]
and
\[
0<\delta_1(h)<1.
\]
The inequality \(T_1>1\) is not a consequence of the \(W\)-constraints alone;
it is a genuine Section 4 side condition, verified in the final application
from the unresolved strip of Proposition 8.1.  Namely, using
\[
x\ll G^{17}\Omega^{-26}X^{O(u)},\qquad
\Omega\gg G^{-1/4}U^{-3/4}X^{-O(u)},
\]
one gets
\[
T_1
\gg H^{1/2}G^{-69/2}U^{-57/2}X^{-O(u)}>1
\]
for \(g<2/18977\) and \(u>0\) sufficiently small.
The positivity is immediate.  For the upper bound,
\[
\delta_1(h)
\ll
H^{-1/2}x^{-5/2}\Omega^{-2}
+H^{-3/2}x^{-1/2}G^{-1}\Omega^{-1}
+\frac{W^6}{H^{1/2}x^{5/2}G^3\Omega^7},
\]
so \(\delta_1(h)<1\) follows from the ambient large-\(X\) inequalities and
from the offset constraint \(W^{12}\ll H^{1/2}x^{5/2}G^3\Omega^7\).  Therefore
the hypotheses of Proposition 4.3 are satisfied on each local piece with
\(N=R\), \(T=T_{\rho,q}\), and tolerance \(\delta_1(h)\).  Summing over the
absolutely many pieces and using \(T_{\rho,q}\asymp T_1\) gives, up to a
harmless logarithm,
\[
\#\{r\text{ in the fixed fiber}:\|\Phi_{\rho,\mathbf u}(r)\|\ll\delta_1(h)\}
\ll
(RT_1)^{1/3}+R\delta_1(h)+R\sqrt{\delta_1(h)/T_1}+1.
\tag{7.8}
\]
The logarithm in Proposition 4.3 is \(X^{o(1)}\) in the present range and is
absorbed by shrinking the absolute constant \(c\) in the \(W\)-constraints.
Here, using \(R\asymp R_0\),
\[
(RT_1)^{1/3}\ll (R_0T_1)^{1/3}
=H^{1/3}x^{-1/3}\Omega^{2/3},
\]
\[
R\sqrt{\delta_0/T_1}\ll G^{3/2}\Omega^{5/2},
\qquad
R\sqrt{\frac{\Omega^2/(RH)}{T_1}}\ll xG\Omega^3,
\qquad
R\sqrt{\frac{S/(Rx^2G^2\Omega^4)}{T_1}}\ll S^{1/2}.
\]
Summing (7.8) over the whole rectangular shift box, multiplying by the fiber
count (7.2), using (7.6), and comparing with the averaged cube lower bound
\(\gg R/W\), we use
\[
\sum 1\ll W^7,\qquad \sum S\ll W^{13},\qquad
\sum S^{1/2}\ll W^{10},\qquad \sum S^{3/2}\ll W^{16}.
\]
This gives the additional constraints
\[
W^8\ll H^{1/6}x^{5/6}G\Omega^{7/3},
\]
\[
W^8\ll H^{1/2}x^{1/2}G^{-1/2}\Omega^{1/2},
\]
\[
W^{11}\ll H^{1/2}x^{1/2}G\Omega^3,
\]
\[
W^8\ll H^{1/2}x^{1/2}G^2\Omega^3,
\]
\[
W^{14}\ll H^{1/6}x^{5/6}G^2\Omega^{22/3},
\]
\[
W^{14}\ll H^{1/2}x^{1/2}G^{1/2}\Omega^{11/2},
\]
\[
W^{17}\ll H^{1/2}x^{1/2}G^2\Omega^8,
\]
\[
W^{14}\ll H^{1/2}x^{1/2}G^2\Omega^8.
\]
The displayed residual square-root term gives in addition
\[
W^8\ll H^{1/2}x^{-1/2},
\qquad
W^{14}\ll H^{1/2}x^{-1/2}G\Omega^5.
\]
Taking roots gives exactly the new constraints listed in the statement, apart
from those already present in the \(\rho_0=0\) branch.  Therefore the assumption
\(M>R/W\) is impossible. ∎

### Proposition 7.3
Let \(W\) satisfy the bounds in Proposition 7.1. Then
\[
\#\mathcal R_a\ll \left(1+\frac{H}{A^2}\right)\frac{R}{W}.
\]

#### Proof
Apply Proposition 7.1 inside the sum over \(j\). The number of relevant \(j\) is \(O(1+H/A^2)\). ∎

---

## 8. Consequences of the two elementary propositions

For a dyadic \(A\)-scale with \(A=\Delta\Omega\), write
\[
\mathbf D(\Omega):=\sum_{a\sim A}\#\mathcal D_a.
\]
The propositions from Sections 5 and 6 imply the following unresolved strip.

### Proposition 8.1
Assume \(0<g<2/18977\), \(\Delta\ge X^{1/100}\), and \(u>0\) is sufficiently small in terms of \(g\). Then \(\#\mathcal D[D,2D]\ll H/U\) unless
\[
x\gg G^{-2}\Omega^{-11/2}X^{-O(u)}
\qquad\text{and}\qquad
x\ll G^{17}\Omega^{-26}X^{O(u)}.
\]

#### Proof
By Proposition 3.2,
\[
\mathbf D(\Omega)
\ll
\left(1+G^{-2/3}\Omega^{-8/3}\right)\sum_{a\sim A}\#\mathcal R_a
\ll X^{O(u)}\sum_{a\sim A}\#\mathcal R_a.
\]
Applying Proposition 6.1 and dividing by \(H\) gives
\[
\frac{\mathbf D(\Omega)}{H}
\ll
X^{O(u)}\left(xG\Omega^2+x^{2/3}G^{4/3}\Omega^{11/3}+H^{-1/2}G^{1/2}\Omega^{5/2}\right).
\]
The last term is
\[
X^{-(1-g)/10+g/2+O(u)}=O(U^{-1}).
\]
The second term is \(O(U^{-1})\) once
\[
x\ll G^{-2}\Omega^{-11/2}X^{-O(u)}.
\]
Under the same condition, the first term is
\[
\ll G^{-1}\Omega^{-7/2}X^{-O(u)}
\ll X^{-g/8+O(u)}=O(U^{-1}),
\]
using \(\Omega\gg G^{-1/4}X^{-O(u)}\).

For Proposition 5.1 we argue similarly. Using
\[
\mathbf D(\Omega)
\ll X^{O(u)}\sum_{a\sim A}\#\mathcal R_a
\ll X^{O(u)}A\cdot \frac{H}{\Delta}\left(
\frac{G^9U^{51}}{\Delta^{1/2}\Omega}
+\frac{G^{17}U^{85}}{\Delta\Omega^{13}}
+\frac{\Delta^2}{H}\frac{G^{17}U^{100}}{\Omega^{27}}
\right),
\]
and substituting \(A=\Delta\Omega\), \(\Delta=H^{1/2}x^{-1/2}\), and \(U^{O(1)}=X^{O(u)}\), we obtain
\[
\frac{\mathbf D(\Omega)}{H}
\ll
X^{O(u)}\left(H^{-1/4}x^{1/4}G^9
+x^{-1}G^{17}\Omega^{-26}
+H^{-1/2}x^{1/2}G^{17}\Omega^{-12}\right).
\]
Since \(\Delta\ge X^{1/100}\), the first term is
\[
X^{-1/200+9g+O(u)}=O(U^{-1}),
\]
and the third term is
\[
X^{-1/100+17g+O(u)}=O(U^{-1}).
\]
The middle term is \(O(U^{-1})\) once
\[
x\gg G^{17}\Omega^{-26}X^{O(u)}.
\]
Thus every dyadic \(\Omega\)-scale outside the displayed strip contributes \(O(H/U)\). Since there are only \(O(\log X)=X^{O(u)}\) such scales, after shrinking \(u\) if necessary this still gives \(O(H/U)\) in total. Hence only the displayed strip remains unresolved. ∎

---

## 9. Global optimization of the final bound

We now combine Proposition 7.3 with the unresolved strip of Proposition 8.1.

For one \(A\)-scale,
\[
\mathbf D(\Omega)\ll \left(1+G^{-2/3}\Omega^{-8/3}\right)\sum_{a\sim A}\#\mathcal D_a.
\]
By Proposition 3.2,
\[
\#\mathcal D_a\ll \left(1+G^{-2/3}\Omega^{-8/3}\right)\#\mathcal R_a\ll X^{O(u)}\#\mathcal R_a.
\]
On the strip of Proposition 8.1, write \(W_{\mathrm{old}}\) for the old
bottleneck coming from the \(\rho_0=0\) branch,
\[
W_{\mathrm{old}}:=H^{1/54}x^{1/54}G^{2/27}\Omega^{8/27}X^{-O(u)}.
\]
The comparison of the original nine constraints is unchanged: on the strip,
all nine old constraints are \(\gg W_{\mathrm{old}}\) for
\(g<2/18977\), after shrinking \(u\) in terms of \(g\).

The new carry branch \(\rho_0\ne0\) contributes the additional constraint
\[
W_{\ne0}:=H^{1/84}x^{5/84}G^{1/7}\Omega^{11/21}X^{-O(u)}.
\]
This is the new bottleneck.  First,
\[
\frac{W_{\mathrm{old}}}{W_{\ne0}}
=H^{5/756}x^{-31/756}G^{-13/189}\Omega^{-43/189}.
\]
Since the exponent of \(x\) is negative, the minimum on the strip occurs at
\(x=G^{17}\Omega^{-26}X^{O(u)}\).  The resulting \(\Omega\)-exponent is
positive, so the minimum in \(\Omega\) occurs at the lower edge
\(\Omega\gg G^{-1/4}X^{-O(u)}\).  Thus
\[
\frac{W_{\mathrm{old}}}{W_{\ne0}}
\gg X^{1/756-1477g/1512+O(u)}\gg1
\]
for \(g<2/18977\) and \(u\) sufficiently small.

The remaining new constraints from Proposition 7.1 are also larger than
\(W_{\ne0}\) on the strip.  The only ratios with a potentially negative
\(G\)-exponent after substitution are
\[
\frac{H^{1/48}x^{5/48}G^{1/8}\Omega^{7/24}}{W_{\ne0}},
\quad
\frac{H^{1/16}x^{1/16}G^{-1/16}\Omega^{1/16}}{W_{\ne0}},
\quad
\frac{H^{1/24}x^{5/24}G^{1/4}\Omega^{7/12}}{W_{\ne0}},
\]
and each is \(\gg X^{c+O(u)-C g}\) with \(c/C>2/18977\).  The other ratios
have still larger positive powers of \(H\), \(x\), \(G\), or \(\Omega\) after
using the same endpoint substitutions.  Hence, throughout the unresolved
strip, we may take
\[
W_*:=W_{\ne0}.
\]

Applying Proposition 7.3 with \(W=W_*\), and using that there are
\(A\asymp\Delta\Omega\) values of \(a\sim A\) and
\(R=HG\Omega^3/\Delta\), gives
\[
\mathbf D(\Omega)
\ll X^{O(u)}\,A\left(1+\frac{H}{A^2}\right)\frac{R}{W_*}.
\]
Since
\[
A\left(1+\frac{H}{A^2}\right)R
\asymp HG\Omega^4\left(1+\frac{x}{\Omega^2}\right),
\]
we get
\[
\frac{\mathbf D(\Omega)}{H}
\ll
X^{O(u)}H^{-1/84}G^{6/7}
\left(\Omega^{73/21}x^{-5/84}+\Omega^{31/21}x^{79/84}\right).
\tag{9.1}
\]

For the first term in (9.1), the exponent of \(x\) is negative, so the worst
case is the lower edge
\[
x=G^{-2}\Omega^{-11/2}X^{-O(u)}.
\]
This gives
\[
X^{O(u)}H^{-1/84}G^{6/7}\Omega^{73/21}
\cdot G^{5/42}\Omega^{55/168}
= X^{O(u)}H^{-1/84}G^{41/42}\Omega^{213/56}.
\]
Using \(\Omega\ll U\), this is \(O(U^{-1})\) provided
\[
H^{-1/84}G^{41/42}U^{269/56}X^{O(u)}\ll1.
\tag{9.2}
\]

For the second term in (9.1), the exponent of \(x\) is positive, so the worst
case is the upper edge
\[
x=G^{17}\Omega^{-26}X^{O(u)}.
\]
This gives
\[
X^{O(u)}H^{-1/84}G^{6/7}\Omega^{31/21}
\cdot G^{17\cdot79/84}\Omega^{-26\cdot79/84}
= X^{O(u)}H^{-1/84}G^{1415/84}\Omega^{-965/42}.
\]
Now the exponent of \(\Omega\) is negative, so the worst case is the lower
edge \(\Omega\gg G^{-1/4}U^{-3/4}X^{-O(u)}\).  Hence
\[
\frac{\mathbf D(\Omega)}{H}
\ll X^{O(u)}H^{-1/84}G^{3795/168}U^{965/56}.
\]
This is \(O(U^{-1})\) provided
\[
H^{-1/84}G^{3795/168}U^{1021/56}X^{O(u)}\ll1.
\tag{9.3}
\]
The condition (9.3) dominates (9.2).  Substituting
\(G=X^g\), \(U=X^u\), and \(H=X^{(1-g)/5}\), it becomes
\[
-\frac{1-g}{420}+\frac{3795}{168}g+\frac{1021}{56}u+O(u)<0,
\]
or equivalently
\[
18977g+15315u<2.
\]
Thus, for every \(g<2/18977\), after choosing \(u>0\) sufficiently small in
terms of \(g\), one has
\[
\mathbf D(\Omega)\ll H/U
\]
for every dyadic \(\Omega\)-scale.  Summing over the
\(O(\log X)=X^{O(u)}\) admissible dyadic \(\Omega\)-scales, and shrinking \(u\)
once more if needed, gives
\[
\#\mathcal D[D,2D]\ll H/U
\]
for every dyadic \(D\).

Returning to the Möbius inversion reduction in Section 1,
\[
\sum_{X\le n\le X+H}\mu^2(n)=\frac6{\pi^2}H+O(H/U).
\]
This proves the theorem.

Finally, for a given \(\varepsilon>0\), choose
\[
g=\frac{2}{18977}-5\varepsilon.
\]
Then
\[
H=X^{(1-g)/5}=X^{1/5-2/94885+\varepsilon},
\]
and the interval \([X,X+H]\) contains a squarefree number for all sufficiently large \(X\). ∎

---

## 10. Summary of the exponent

The argument proves:

### Theorem 10.1
For every \(\varepsilon>0\), all sufficiently large \(X\) contain a squarefree number in
\[
[X,\ X+X^{1/5-2/94885+\varepsilon}].
\]

Equivalently,
\[
\theta_* \le \frac15-\frac{2}{94885}.
\]

---
