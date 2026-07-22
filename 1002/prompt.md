For a real number (t), write
[
{t}=t-\lfloor t\rfloor\in[0,1)
]
for its fractional part. Throughout, (\log) denotes the natural logarithm.

For every integer (n\ge2) and every (\alpha\in(0,1)), define
[
f(\alpha,n)
===========

\frac1{\log n}
\sum_{1\le k\le n}
\left(\frac12-{\alpha k}\right).
]

For every real number (c), define
[
F_n(c)
======

\left|
\left{
\alpha\in(0,1):
f(\alpha,n)\le c
\right}
\right|,
]
where (|\cdot|) denotes Lebesgue measure. Since ((0,1)) has measure (1), (F_n) is the distribution function of (f(\alpha,n)) when (\alpha) is chosen uniformly from ((0,1)).

Resolve the following Erdős problem completely:

Does (f(\alpha,n)), viewed as a random variable in (\alpha\in(0,1)), possess an asymptotic distribution function as (n\to\infty)?

More precisely, determine whether there exists a non-decreasing function
[
g:\mathbb R\to[0,1]
]
such that
[
\lim_{c\to-\infty}g(c)=0,
\qquad
\lim_{c\to+\infty}g(c)=1,
]
and
[
\lim_{n\to\infty}F_n(c)=g(c)
]
for every real number (c).

This pointwise convergence for every (c\in\mathbb R) is the exact requirement of the problem. Do not replace it by the weaker standard notion of convergence in distribution, which requires convergence only at continuity points of the limiting distribution function. Conversely, do not impose additional continuity or right-continuity assumptions on (g) that are not part of the stated problem.

Assume for purposes of this task that a complete resolution exists, but do not assume in advance that the answer is affirmative or negative. A complete solution must prove exactly one of the following two statements.

Affirmative resolution:

There exists a non-decreasing function (g:\mathbb R\to[0,1]) satisfying
[
\lim_{c\to-\infty}g(c)=0,
\qquad
\lim_{c\to+\infty}g(c)=1,
]
such that for every fixed real number (c),
[
\lim_{n\to\infty}
\left|
\left{
\alpha\in(0,1):
\frac1{\log n}
\sum_{k=1}^{n}
\left(\frac12-{\alpha k}\right)
\le c
\right}
\right|
=======

g(c).
]

A complete affirmative solution must prove convergence for every real (c), verify the two boundary conditions on (g), and characterize (g) rigorously enough to establish these claims. An elementary closed formula for (g) is not required unless the argument produces one, because the original question asks for existence rather than a particular closed-form expression.

Negative resolution:

No non-decreasing function (g) satisfying the stated boundary conditions has the required pointwise convergence property.

Equivalently, a complete negative solution must rigorously establish at least one of the following:

* there exists a fixed real number (c) for which the sequence (F_n(c)) does not converge; or

* (F_n(c)) converges for every real (c), but the resulting pointwise limit
  [
  h(c)=\lim_{n\to\infty}F_n(c)
  ]
  fails at least one of the required boundary conditions
  [
  \lim_{c\to-\infty}h(c)=0,
  \qquad
  \lim_{c\to+\infty}h(c)=1.
  ]

The second possibility corresponds to probability mass escaping to (+\infty) or (-\infty). Since every (F_n) is non-decreasing, any pointwise limit (h), if it exists everywhere, is automatically non-decreasing. Thus these alternatives capture the exact ways in which the requested function (g) can fail to exist.

Partial progress does not count unless it implies exactly one of the two complete resolutions above. In particular, the following are insufficient:

* proving convergence only for almost every (c);
* proving convergence only at continuity points of a candidate limiting distribution;
* proving convergence only along a subsequence of integers (n);
* producing two subsequential limits without proving that they differ in a way that rules out the required full limit;
* proving only tightness of the family (f(\alpha,n));
* proving only boundedness of moments, convergence of selected moments, or convergence of characteristic functions on a restricted range;
* proposing a candidate limiting distribution without proving convergence of (F_n(c)) for every (c);
* proving convergence after additional centering, rescaling, truncation, smoothing, or averaging not present in the original definition;
* replacing the normalization (1/\log n) by another normalization;
* averaging (F_n(c)) over (n), whether by Cesàro, logarithmic, or another summation method;
* proving a limit theorem for a fixed typical (\alpha), rather than the distribution over uniformly chosen (\alpha);
* proving only almost-sure, in-probability, or distributional behavior of a different random model;
* restricting (\alpha) to irrational numbers, badly approximable numbers, bounded-type numbers, rational numbers, or another subclass without proving that the restriction leaves the required distribution unchanged;
* modifying the values of the sawtooth term at points where (\alpha k\in\mathbb Z) without justifying that the modification affects only a null set;
* replacing
  [
  \frac12-{\alpha k}
  ]
  by a related periodic function without proving exact equivalence for the required distributional statement;
* computing (F_n(c)) numerically for finitely many (n);
* giving only heuristic evidence from continued fractions, independence assumptions, random-walk analogies, or Gaussian approximations;
* proving convergence of the limsup and liminf without proving that they coincide;
* reducing the problem to another unproved limit theorem of comparable strength.

Standard proved theorems from uniform distribution theory, discrepancy theory, continued fractions, metric Diophantine approximation, ergodic theory, dynamical systems, harmonic analysis, Fourier analysis, probabilistic number theory, transfer operators, renewal theory, or probability may be used, but they must be stated accurately and applied with all necessary hypotheses, normalizations, and uniformity.

Use multiagent v2 aggressively and dynamically. You have up to 4 concurrent agents available. Do not use a fixed assignment such as “N agents for strategy X.” Instead, manage the search using the following heuristics:

* Begin with a genuinely diverse portfolio of approaches. Agents should explore substantially different formulations, invariants, reductions, Fourier expansions of the sawtooth function, discrepancy sums, continued-fraction decompositions, Farey partitions, Gauss-map and transfer-operator methods, renewal structures, characteristic functions, moment calculations, tightness and anti-concentration, subsequential constructions, rational approximations, exact finite-(n) decompositions, and computational sanity checks.

* Do not tell most agents the currently favored approach. Preserve independence during early rounds so that agents do not all converge to the same attractive but incomplete Gaussian heuristic, continued-fraction approximation, or moment calculation.

* Maintain an explicit registry of approach families. Group agents by the mathematical idea they are using, not by superficial wording. If many agents converge to one family, redirect some of them toward underexplored formulations.

* Do not allow one approach to dominate merely because it suggests a familiar candidate distribution. A route that ends at an unproved limit theorem, independence principle, mixing assertion, or tightness statement equivalent in strength to the original problem is not close to completion unless it supplies a genuinely new proof of that statement.

* When an approach stalls at a theorem-strength missing lemma, mark that route as blocked. Only continue assigning agents to it if someone proposes a materially new mechanism, invariant, decomposition, quantitative estimate, or convergence principle.

* Keep several incompatible proof routes alive through multiple rounds. Maintain both universal-convergence routes and nonconvergence or escape-of-mass routes until one side is rigorously ruled out. Cross-pollinate ideas only after independent agents have developed them far enough to expose their real strengths and gaps.

* Use computational agents throughout. They should compute (F_n(c)) accurately, exploit the piecewise structure in (\alpha), investigate moments and characteristic functions, test candidate limiting laws, search for oscillating subsequences, identify exceptional scales associated with rational approximations, and find counterexamples to proposed intermediate lemmas. Computation is evidence unless it is converted into a rigorous asymptotic proof or an exact certificate completing a valid reduction.

* Use adversarial agents throughout. Every candidate proof must be checked for:

  * convergence for every real (c), rather than only continuity points or almost every (c);
  * the exact normalization (1/\log n);
  * the exact summation range (1\le k\le n);
  * the precise fractional-part convention ({t}\in[0,1));
  * the distinction between randomness in (\alpha) and asymptotics for a fixed (\alpha);
  * convergence along the full sequence (n\to\infty), rather than a subsequence;
  * tightness and both boundary conditions at (\pm\infty);
  * unjustified interchange of limits in (n), (c), Fourier truncation, continued-fraction depth, or moment order;
  * use of characteristic functions without proving the hypotheses needed to recover the required pointwise distribution functions;
  * moment convergence without moment determinacy or tightness;
  * assuming independence among the terms ({\alpha k});
  * treating the sequence ({\alpha k}) as independent uniform random variables;
  * applying ergodic theorems that concern a fixed irrational rotation when the problem concerns the distribution over (\alpha);
  * ignoring rational or near-rational values of (\alpha) when they may influence the limiting distribution;
  * numerical evidence masquerading as proof;
  * circular use of a limit theorem equivalent to the desired conclusion.

* Require agents to return concrete lemmas, decompositions, equations, probability estimates, characteristic-function bounds, moment identities, algorithms, code outputs, exact finite-(n) formulas, or counterexamples to proposed sublemmas. Reject status reports, vague optimism, and claims that an unproved mixing, independence, tightness, or uniform-integrability statement is “routine.”

* The root agent should repeatedly synthesize, challenge, redirect, and launch new rounds. Do not stop after the first wave fails. Produce a complete affirmative proof or a complete negative argument only if it survives adversarial audit; otherwise report only the strongest rigorously proved derivation and its exact remaining gap.

Do not return merely because current approaches fail or agents report theorem-strength gaps. Continue launching new rounds, reopening blocked approaches only when there is a genuinely new mechanism, and searching for fresh formulations.

Return only when the existence of the asymptotic distribution function, in the exact pointwise sense stated above, has been completely resolved and the argument survives adversarial audit. Do not return a reduction, partial result, isolated missing lemma, subsequential limit, moment calculation, finite computation, numerical guess, “best effort” summary, or explanation of why the problem is difficult.

Do not stop, return, or give up until you have found a complete and rigorous solution. Continue exploring every plausible approach, repairing failed arguments, and developing new ones until the problem is fully resolved.

Public search may be used only for ordinary mathematical background or standard named theorems, not to search for a solution to this exact Erdős problem or benchmark. Do not search the public web merely to determine whether this problem is open, and do not answer that it is open.
