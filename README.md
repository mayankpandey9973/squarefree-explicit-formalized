# Squarefree numbers in short intervals 

This repository formalizes a proof of the result in https://arxiv.org/abs/2401.13981 
with exponents made explicit.

Specifically, we show that for all $\varepsilon > 0$, $X > $ and $H > X^{1/5 - \eta + \varepsilon}$, we have
\[
\biggl| \sum_{X < n \le X + H} \mathbf{1}_{n\text{ squarefree}} - \frac{6}{\pi^2}H \biggr|\le H X^{-\varepsilon}
\]


The main novelty required to make this explicit was a bare-hands execution of the contents of 
section 6 of the original paper, which appeals to work of Green and Tao 
(https://arxiv.org/abs/0709.3562). Matters are significantly simplified by the fact that as 
we only desire upper bounds rather than equidistribution for a nilsequence, we can 
execute our arguments purely in physical space. In addition, carrying with the fractional part
is not an issue: we can consider the cases {x} + {y} = {x + y} and {x} + {y} = {x + y} + 1
without any attempt at detecting the two cases.


## Rough outline of AI usage

Most of the labor of this effort was carried out by AI. The execution of the




