# Abercrombie's sequence
This is the formalised proof that a certain integer sequence, which apparently (and unexpectedly) leads to a bijection between nonnegative integers $\mathbb{N}_0$ and $\mathbb{N}_0\times\mathbb{N}_0$, is well-defined.

For a nonnegative integer $k$, the sequences $h_k(m)$ and $d_k(m)$ are defined recursively. First, $h_k(1) = k$. For $m>1$, let $r_k(m) = q_k(m)\cdot m$ be the smallest multiple of $m$ which is $\geqslant h_k(m-1)$, and $d_k(m) = r_k(m) - h_k(m-1)$. Then $h_k(m)$ is defined to be $r_k(m) + d_k(m)$. Informally, $h_k(m)$ is obtained by "reflecting" $h_k(m-1)$ in $r_k(m)$.

**Theorem.** $d_k(m)$ is eventually 2-periodic.

Let $b_k$ (resp. $c_k$) be the eventually constant value of $d_k(m)$ for even (resp. odd) $m$. OEIS [A135317](https://oeis.org/A135317) by Alex Abercrombie is the sequence of $c_{2k}$, and the notation used in that entry agrees with the definitions introduced above. That sequence is well-defined because the theorem above is true, and the proof of that theorem is what given and formalised in Lean here.

## Proof
In the Lean code, $h_k(m)$ is `h k m`, $r_k(m)$ is `r k m`, $q_k(m+1)$ is `q k m`, $d_k(m+1)$ is `bc k m`.

Note that if for some $m$ it happens that $q_k(m) = q_k(m+1)$, then $d_k(m)$ become 2-periodic from that point, as desired (lemmas `need_q_const` and `q_stays_const`).

For a fixed $k\geqslant0$, initially (for small $m$) we have $q_k(m) \geqslant m$. While this condition holds, as $m$ increases, $q_k(m)$ doesn't increase (lemma `q_nonincreasing`): $h_k(m) = q_k(m)\cdot m + d_k(m) < q_k(m)\cdot m + m \leqslant q_k(m)\cdot m + q_k(m) = q_k(m)\cdot(m+1)$, so $q_k(m+1) \leqslant q_k(m)$, otherwise $q_k(m+1)\cdot(m+1)$ wouldn't be the smallest multiple of $m+1$ which is $\geqslant h_k(m)$.

If $q_k(m+1) = q_k(m)$, then we're done, so from now on suppose $q_k(m)$ strictly decreases as $m$ increases until $q_k(m) < m$.

Note however that if $q_k(m-1) > m$, then $q_k(m)$ is at least $m$ (lemma `q_decr_not_so_fast`): suppose not, i.e. $q_k(m) \leqslant m-1$, then $(m+1)\cdot(m-1) \leqslant q_k(m-1)\cdot(m-1) \leqslant h_k(m-1) \leqslant q_k(m)\cdot m \leqslant (m-1)\cdot m$, contradiction.

Therefore for some $m$ we have either (A) $q_k(m) = m$ or (B) $q_k(m-1) = m$ (`AB_alternative`).
* Case (A): then $m^2 = q_k(m)\cdot m \leqslant h_k(m) \leqslant q_k(m+1)\cdot(m+1)$, which implies $q_k(m+1) = m$, as desired.
* Case (B): then $m\cdot(m-1) = q_k(m-1)\cdot(m-1) \leqslant h_k(m-1) \leqslant q_k(m)\cdot m$, which implies $q_k(m) = m = q_k(m-1)$ (and then we're done) or $m-1$. Suppose the latter, then $h_k(m) = h_k(m-1) = m\cdot(m-1)$. At this point the condition $q_k(m) \geqslant m$ no longer holds, but we can show directly that $q_k(m+1) = m-1 = q_k(m)$: this is equivalent to $(m-2)\cdot(m+1) < h_k(m) \leqslant (m-1)\cdot(m+1)$, which is true.

## Possible further work
The most remarkable thing about Abercrombie's $b_k$ and $c_k$ is his observation (given here in a slightly different form) that $f : k\mapsto(b_k,c_k)$ is apparently a bijection $\mathbb{N}_0 \to \mathbb{N}_0\times\mathbb{N}_0$. This is not proved here.

It appears that $f = g \circ p$, where $g$ is another bijection $\mathbb{N}_0 \to \mathbb{N}_0\times\mathbb{N}_0$ called "stripe enumeration" or "boustrophedonic Cantor enumeration" (see [A319571](https://oeis.org/A319571)), and $p$ is a permutation $\mathbb{N}_0 \to \mathbb{N}_0$ such that $p^{-1}$ is defined "reverse the order in each pair, skip one pair, reverse the order in each triple, skip one triple, and so on" (see [A249990](https://oeis.org/A249990)). Proving this observation would provide a different and possibly more insightful proof that $f$ is well-defined (and bijective).
