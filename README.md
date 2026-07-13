# Formalization of "[Nearly tight exponents for off-diagonal Ramsey numbers](https://arxiv.org/abs/2605.28793)" by Domagoj Bradač

## Formalization by Trellis

## Paper targets

This formalization corresponds to **v3** of the paper.

| Label | Node | Statement |
|---|---|---|
| `thm:main` | `Tablet.MainTheorem` | For any $s\ge 3$, there is a positive constant $c_s$ such that for any $k\ge 2$, $r(s,k)\ge c_s\,k^{s-1}/(\log k)^{2s-4}$. |
| `thm:off-diagonal-general` | `Tablet.OffDiagonalGeneralTheorem` | For every $\delta>0$, there exists a constant $L$ such that for all positive integers $s\ge L$ and $k\ge Ls$, $r(s,k)\ge (k/s)^{(1-\delta)s}$. |
| `thm:k-Ck` | `Tablet.LinearOffDiagonalTheorem` | Let $C>1$ be fixed. Then, for all sufficiently large $s$, $r(s,\lceil Cs\rceil)\ge \left(2^{1-1/(2C)}\right)^s$. |
| `thm:close` | `Tablet.CloseToDiagonalTheorem` | Let $s\to\infty$ and let $a$ be a nonnegative integer such that $a=o(s)$. Then $r(s,s+a)\ge (1+o(1))\frac{s}{e}\cdot 2^{(s+a-1)/2-a^2/(2s)}$. |
| `thm:multicolor` | `Tablet.MulticolorTheorem` | For every fixed $\ell\ge 3$, $r(s;\ell)=\Omega(2^{(\ell-1)s/2})$. |

## Semantic closure

| Node | Definition |
|---|---|
| `Tablet.RamseyProperty` | The predicate $R(s,k,n)$ says that every simple graph on $n$ vertices contains either a clique of size $s$ or an independent set of size $k$. |
| `Tablet.RamseyNumber` | The two-color Ramsey number $r(s,k)$ is the least integer $n$ such that every graph on $n$ vertices contains a clique of size $s$ or an independent set of size $k$. |
| `Tablet.MulticolorRamseyProperty` | The predicate $R_\ell(s,n)$ says that every $\ell$-coloring of the edges of the complete graph on $n$ vertices contains a monochromatic clique of size $s$. |
| `Tablet.MulticolorRamseyNumber` | The diagonal multicolor Ramsey number $r(s;\ell)$ is the least integer $n$ such that every $\ell$-coloring of the edges of $K_n$ contains a monochromatic clique of size $s$. |

## History: two Trellis runs (paper v1, then revision to v3)

This repository's history contains two complete autonomous Trellis runs, one commit
per supervisor checkpoint:

- **Original run** (tag `paper-v1`, 2026-05-28..30): formalized
  [arXiv:2605.28793v1](https://arxiv.org/abs/2605.28793v1). In v1, `thm:main` gave
  $r(s,k)\ge c_s\,k^{s-2}/(\log k)^{2s-6}$ for $s\ge 4$.
- **Revision run** (tag `paper-v3`, 2026-06-28..29): starting from the commit
  `revision setup: imported clean basis + revision scaffolding`, Trellis's revision
  mode updated the finished formalization to
  [arXiv:2605.28793v3](https://arxiv.org/abs/2605.28793v3), whose `thm:main` is the
  stronger bound stated above ($k^{s-1}/(\log k)^{2s-4}$, now for all $s\ge 3$).
  The revision run diffed the two paper versions (`paper/revision/old.tex` vs
  `paper/revision/new.tex`), re-stated the affected target, rebuilt the supporting
  proof tree, and re-verified; the other four paper targets and the semantic-closure
  definitions are unchanged from the original run. Cycle numbering in the
  revision run's commit messages restarts at 1.

As in the original run, the only human input to the revision run was approval of the
revised theorem statements at the human gate; no mathematical content, proof steps,
or formalization hints were supplied by hand.
