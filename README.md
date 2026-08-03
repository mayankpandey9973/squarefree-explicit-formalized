# Squarefree numbers in short intervals 

This repository formalizes a proof of the result in https://arxiv.org/abs/2401.13981 
with exponents made explicit.

Specifically, we show that with $\eta = 2/90935$, for all $\varepsilon > 0$, $X > \exp(10^{32}/\varepsilon^2)$
and $H > X^{1/5 - \eta + \varepsilon}$, there exists a squarefree number in $[X, X + H]$


The main novelty required to make this explicit was a bare-hands execution of the contents of 
section 6 of the original paper, which appeals to work of Green and Tao 
(https://arxiv.org/abs/0709.3562). Matters are significantly simplified by the fact that as 
we only desire upper bounds rather than equidistribution for a nilsequence, we can 
execute our arguments purely in physical space. In addition, carrying with the fractional part
is not an issue: we can consider the cases {x} + {y} = {x + y} and {x} + {y} = {x + y} + 1
without any attempt at detecting the two cases at the cost of losing a constant factor.


## Rough outline of AI usage/workflow

Most of the labor of this effort was carried out by AI. The execution of the section 6 argument in the
original paper was carried out by giving an outline of the argument to GPT5.4 Pro, which was then 
used to combine this with the original paper (for which explicit exponents in all but section 6 had already
been worked out by hand) to produce an md. 
Then, Claude Code along with Codex (in the end, the former calling the latter) was used to generate the lean 
over the course of about 2-3 weeks. 

There was an earlier, nearly successful, less supervised attempt, which resulted an unmanageable, ~500k line
attempt nearly entirely by Codex, which did inform the second 111k line attempt. 
