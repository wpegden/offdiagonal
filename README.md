# Formalization of "[Nearly tight exponents for off-diagonal Ramsey numbers](https://arxiv.org/abs/2605.28793)" by Domagoj Bradač

## Formalization by Trellis

## Paper targets

| Label | Node | Statement |
|---|---|---|
| `thm:main` | `Tablet.MainTheorem` | For any $s\ge 4$, there is a positive constant $c_s$ such that for any $k\ge 2$, $r(s,k)\ge c_s\,k^{s-2}/(\log k)^{2s-6}$. |
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
