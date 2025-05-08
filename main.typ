#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#set heading(numbering: "1A.1")
#set math.equation(numbering: "(1)")

#let problem = thmbox("problem", "Problem", fill: rgb("#eeffee")).with(numbering: "1A.1")
#let solution = thmplain("solution", "Solution").with(numbering: "1A.1")
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#ffeeee")).with(numbering: "1A.1")
#let proof = thmplain("proof", "Proof").with(numbering: "1A.1")
#let sect = math.inter

#align(
  center,
  text(17pt)[
    *Solutions to exercises of Axler's\
  "Measure, Integration and Real Analysis"*
  ],
)

= Riemann Integration

== Part A

#problem[
  Suppose $f: [a, b] -> RR$ is a bounded function such that
  $ L(f, P, [a, b]) = U(f, P, [a, b]) $
  for some partition $P$ of $[a, b]$. Prove that $f$ is constant on $[a, b]$.
]

#solution[
  Suppose $P$ is the partition $a = x_0 < x_1 < ... < x_n = b$, then
  $
    0 = U(f, P, [a, b]) - L(f, P, [a, b]) = sum_(j = 1)^n (x_j - x_(j-1))
    (sup_([x_(j - 1), x_j]) f - inf_([x_(j - 1), x_j]) f)
  $

  Then, it becomes trivial that we must have
  $ sup_([x_(j - 1), x_j]) f - inf_([x_(j - 1), x_j]) f = 0, forall j = 1, ..., n $

  This is equivalent to the fact that $f$ is constant on $[x_(j-1), x_j]$, for
  all $j = 1, ..., n$. Hence $f$ is constant on $[a, b]$.
]

#problem[
  Suppose $a <= s < t <= b$. Define $f: [a, b] -> RR$ by
  $ f(x) = cases(1 "if" s < x < t,  0 "otherwise") $. Prove that $f$ is Riemann
  integrable on $[a, b]$, and that $integral_a^b f = t - s$.
]

#solution[
  Let $P_epsilon$ be the partition $a, s + epsilon, t - epsilon, b$ for some
  sufficiently small $epsilon > 0$ such that $a < s + epsilon < t - epsilon < b$.

  It is trivial to see that:
  $
    L(f, P_epsilon, [a, b]) &= t - s - 2epsilon, \
    "and" U(f, P_epsilon, [a, b]) &= t - s + 2epsilon
  $

  Now, consider an arbitrary partition $P$ of $[a, b]$, we have:
  $ L(f, P, [a, b]) <= U(f, P_epsilon, [a, b]) = t - s + 2epsilon $

  Letting $epsilon$ go to zero and taking the supremum of the left hand side, we
  have:
  $ sup_P L(f, P, [a, b]) <= t - s $

  But, $L(f, P_epsilon, [a, b]) = t - s - 2epsilon$, which converges to $t - s$
  as $epsilon$ goes to zero. Hence, equality must hold: $sup_P L(f, P, [a, b]) = t - s$.

  Similarly, it is true that $inf_P U(f, P, [a, b]) = t - s$. Hence, $L(f, [a,
  b]) = U(f, [a, b]) = t - s$, QED.
]

#problem[
  Suppose $f: [a, b] -> RR$ is a bounded function. Prove that $f$ is Riemann
  integrable if and only if for each $epsilon > 0$ there exists a partition $P$
  of $[a, b]$ such that
  $ U(f, P, [a, b]) - L(f, P, [a, b]) < epsilon $
]

#solution[
  If $f$ is Riemann integrable, then denote $I = integral_a^b f$. Then,
  $ I = inf_P U(f, P, [a, b]) - sup_P L(f, P, [a, b]), $
  which means for every $epsilon' > 0$, there exists partitions $P_1, P_2$ such
  that
  $ U(f, P_1, [a, b]) <= I + epsilon' "and" L(f, P_2, [a, b]) >= I - epsilon'. $

  Let $P$ be the combination of the two partitions, then:
  $ U(f, P, [a, b]) <= I + epsilon' "and" L(f, P, [a, b]) >= I - epsilon. $

  Hence, $U(f, P, [a, b]) - L(f, P, [a, b]) <= 2epsilon'$, so by taking $epsilon' =
  1/2 epsilon$, we have $U(f, P, [a, b]) - L(f, P, [a, b]) < epsilon$.

  Now, assuming the opposite, suppose for every $epsilon > 0$, there exists a
  partition $P$ such that $U(f, P, [a, b]) - L(f, P, [a, b]) < epsilon$. From
  this, we must have $U(f, [a, b]) - L(f, [a, b]) < epsilon$ for every $epsilon
  > 0$. This can only hold if the left hand side expression is 0, which means
  that $f$ is Riemann integrable.
]

#problem[
  Suppose $f, g: [a, b] -> RR$ is Riemann integrable. Prove that $f + g$ is also
  Riemann integrable and
  $ integral_a^b (f + g) = integral_a^b f + integral_a^b g $
]

#solution[
  Let $P$ be a partition of $[a, b]$, then
  $
    L(f + g, P, [a, b]) >= L(f, P, [a, b]) + L(g, P, [a, b]) >= L(f, [a, b]) +
    L(g, [a, b]), \
    "and" U(f + g, P, [a, b]) <= U(f, P, [a, b]) + U(g, P, [a, b]) <= U(f, [a,
        b]) + U(g, [a, b])
  $

  Taking the infimum/supremum of the left hand sides yields
  $
    L(f + g, [a, b]) >= L(f, [a, b]) + L(g, [a, b]) = U(f, [a, b]) + U(g, [a,
        b]) >= U(f + g, [a, b])
  $
  The middle equality holds since $f$ and $g$ is Riemann integrable on $[a, b]$.
  Now, we have $L(f+g, [a, b]) >= U(f+g, [a, b])$, which must be an equality,
  so $f+g$ is Riemann integrable on $[a, b]$ and
  $ integral_a^b (f + g) = integral_a^b f + integral_a^b g $
  holds.
]

#problem[
  Suppose $f, g: [a, b] -> RR$ is Riemann integrable. Prove that $f - g$ is also
  Riemann integrable and
  $ integral_a^b (f - g) = integral_a^b f - integral_a^b g $
]

#solution[
  For every partition $P$ of $[a, b]$, we have:
  $ L(f, P, [a, b]) = -U(-f, P, [a, b]) "and" U(f, P, [a, b]) = -L(-f, P, [a, b]) $
  From this, it should be trivial to solve this problem.
]

#problem[
  Suppose $f: [a, b] -> RR$ is Riemann integrable. Suppose $g: [a, b] -> RR$ is
  a function such that $g(x) = f(x)$ for all except finitely many $x in [a, b]$.
  Prove that $g$ is also Riemann integrable on $[a, b]$ and
  $ integral_a^b g = integral_a^b f $
]

#solution[
  We will concern ourselves with the easy case where $f(x) = 0$ for all $x in
  [a, b]$. Then, if $x_1 < x_2 < ... < x_n$ are the only values of $x$ such that
  $g(x_i) != 0, forall i = 1, ..., n$, then the partition $P_epsilon$ with $a < x_1 -
  epsilon < x_1 + epsilon < x_2 - epsilon < x_2 + epsilon < ... < x_n - epsilon
  < x_n + epsilon < b$ will yields the following result
  $
    U(f, P, [a, b]) &= 2epsilon sum_(i = 1)^n max{0, g(x_i)}, \
    "and" L(f, P, [a, b]) &= 2epsilon sum_(i = 1)^n min{0, g(x_i)}.
  $
  Letting $epsilon -> 0$ shows that $U(f, [a, b]) <= 0 <= L(f, [a, b])$, so we
  must have $ integral_a^b g = 0 $.

  Back to the general case, since the function $g - f$ satisfies the conditions
  of $g$ as above, $g - f$ must be Riemann integrable on $[a, b]$, and that
  $integral_a^b (g - f) = 0$. Hence, $g$, the sum of two Riemann integrable
  functions $f$ and $g-f$, must also be Riemann integrable on $[a, b]$, and
  $ integral_a^b g = integral_a^b f + integral_a^b (g - f) = integral_a^b f $
]

#problem[
  Suppose $f: [a, b] -> RR$ is a bounded function. For $n in ZZ^+$, let $P_n$
  denote the partition that divides $[a, b]$ into $2^n$ intervals of equal size.
  Prove that
  $
    L(f, [a, b]) = lim_(n -> infinity) L(f, P_n, [a, b]) "and" U(f, [a, b]) =
    lim_(n -> infinity) U(f, P_n, [a, b]).
  $
]

#solution[
  The sequence $l_n = L(f, P_n, [a, b])$ is non-decreasing, so $lim_(n -> infinity)
   L(f, P_n, [a, b])$ definitely exists. Denote this limit as $L$, so $L$ must
  be at least as large as $L(f, [a, b])$. Our aim is to prove that equality
  actually holds here.

  For every partition $Q$ of $[a, b]$, denote $Q_n$ as the combination of $P_n$
  and $Q$. Then,
  $ L(f, [a, b]) = L(f, Q, [a, b]) <= L(f, Q_n, [a, b]) $

  We will establish an upper bound for $L(f, Q_n, [a, b]) - L(f, P_n, [a, b])$.
  Note that these two only differs at most $m$ elements (where $m$ is the
  number of partition points (excluding $a$ and $b$) of $Q$), so this difference
  is basically $O(m w delta)$, where $w$ is the maximum width of a partitioned
  interval (which is $(b-a)/2^n)$, $delta$ is the maximum difference between two
  values of $f(x)$ and $f(y)$ for some $x, y in [a, b]$.

  $m$ is bounded (since $Q$ stays constant), $delta$ is also bounded by
  $sup_[a, b] f  - inf_[a, b] f$ (which is finite since $f$ is bounded) while
  $w -> 0$. Hence, this big-O term converges to $0$ as $n -> infinity$. This
  big-O thingy is not really rigorous, but it should be trivial to make it
  rigorous from here. Anyways, since $L(f, Q_n, [a, b]) - L(f, P_n, [a, b]) ->
  0$, so does $L(f, P_n, [a, b]) - L(f, [a, b])$. Hence,

  $ lim_(n -> infinity) L(f, P_n, [a, b]) = L(f, [a, b]). $

  Needless to say, the other conclusion can be proven similarly.
]

#problem[
  Suppose $f: [a, b] -> RR$ is Riemann integrable. Prove that
  $
    integral_a^b f = lim_(n -> infinity) (b-a) / n sum_(j = 1)^n f(a +
      (j(b-a)) / n).
  $
]

#solution[
  This follows the same logic as the previous exercise. Note that since $f$ is
  Riemann integrable, it must also be bounded by definition.
]

#problem[
  Suppose $f: [a, b] -> RR$ is Riemann integrable. Prove that if $c, d in RR$
  and $a <= c < d <= b$, then $f$ is Riemann integrable on $[c, d]$.
]

#solution[
  For every $epsilon > 0$, there exists a partition $P$ of $[a, b]$ such that
  $ U(f, P, [a, b]) - L(f, P, [a, b]) < epsilon $

  Adding the points $c$ and $d$ to $P$ yields a new partition $P'$ of $[a, b]$,
  which must satisfy
  $ U(f, P', [a, b]) - L(f, P', [a, b]) <= U(f, P, [a, b]) - L(f, P, [a, b]) < epsilon $

  From the definition of lower and upper Riemann sums, we must have the
  following
  $
    U(f, P'', [c, d]) - L(f, P'', [c, d]) <= U(f, P, [a, b]) - L(f, P, [a, b]) <
    epsilon,
  $
  where $P''$ is $P'$ restricted to the interval $[c, d]$, QED.
]

#problem[
  Suppose $f: [a, b] -> RR$ is a bounded function and $c in (a, b)$. Prove that
  $f$ is Riemann integrable on $[a, b]$ if and only if $f$ is Riemann integrable
  on $[a, c]$ and $f$ is Riemann integrable on $[c, b]$. Furthermore, prove that
  if these conditions hold, then:
  $
    integral_a^b f = integral_a^c f + integral_c^b f.
  $
]

#solution[
  Using the previous exercise, it should be trivial to prove that $f$ is Riemann
  integrable on $[a, c]$ and $[c, b]$ if $f$ is Riemann integrable on $[a, b]$.

  Now, if $f$ is Riemann integrable on the two intervals, for any $epsilon > 0$,
  there exists partitions $P_1$ and $P_2$ such that:

  $
    I_1 - epsilon < L(f, P_1, [a, c]) <= U(f, P_1, [a, c]) < I_1 + epsilon, \
    "and" I_2 - epsilon < L(f, P_2, [c, b]) <= U(f, P_2, [c, b]) < I_2 + epsilon,
  $
  where $I_1 = integral_a^c f$ and $I_2 = integral_c^b f$.

  Then, the combined partition $P$ of $P_1$ and $P_2$ on $[a, b]$ must satisfy
  $ I_1 + I_2 - 2epsilon < L(f, P, [a, b]) <= U(f, P, [a, b]) < I_1 + I_2 + 2epsilon $

  From this it is trivial to conclude the exercise.
]

#problem[
  Suppose $f$: $[a, b] -> RR$ is Riemann integrable. Define $F: [a, b] -> RR$ by
  $ F(t) = cases(0 "if" t = a, integral_a^t "if" t in (a, b]). $
  Prove that $F$ is continuous on $[a, b]$.
]

#solution[
  - $f$ is left-continuous at $t = a$: This is equivalent to proving
    $ lim_(t -> a^+) integral_a^t f(t) = 0 $
    Denote $P$ as the trivial partition containing only $a$ and $t$, since
    $integral_a^t f(t) = U(f, [a, t]) <= U(f, P, [a, t]) = (t - a) sup_[a, t]
      f <= (t - a) sup_[a, b] f -> 0$ as $t -> a^+$.
  - $f$ is right-continuous at $t = b$ and $f$ is continuous at every $y in (a,
  b)$: this can be proven similarly as above.
]

#problem[
  Suppose $f: [a, b] -> RR$ is Riemann integrable. Prove that $|f|$ is Riemann
  integrable and that $ abs(integral_a^b f) <= integral_a^b |f|. $
]

#solution[
  For any interval $I$, we have
  $ 0 <= sup_I |f| - inf_I |f| <= sup_I f - inf_I f, $
  therefore, for every partitions $P$ of $[a, b]$, we have
  $ U(|f|, P, [a, b]) - L(|f|, P, [a, b]) <= U(f, P, [a, b]) - L(f, P, [a, b]). $
  Using the epsilon thing, we can see that $|f|$ is Riemann integrable.

  To prove the inequality, it suffices to note that $|f| plus.minus f$ is always
  non-negative, and therefore have non-negative Riemann integrals.
  Hence, $ integral_a^b |f| >= max{integral_a^b (|f| - f) + integral_a^b f,
  integral_a^b (f + |f|) - integral_a^b f} >= abs(integral_a^b f) $.
]

#problem[
  Suppose $f: [a, b] -> RR$ is an increasing function, meaning that $c, d  in
  [a, b]$ with $c < d$ implies $f(c) <= f(d)$. Prove that $f$ is Riemann
  integrable on $[a, b]$.
]

#solution[
  Consider the uniform partition $P_n$ of $[a, b]$ into $N = 2^n$ subintervals, then
  $
    L(f, P_n, [a, b]) = 1 / N sum_(j = 1)^N f(a + (j - 1)(b-a) / N), \
    "and" U(f, P_n, [a, b]) = 1 / N sum_(j = 1)^N f(a + j(b-a) / N).
  $

  Hence,
  $ U(f, P_n, [a, b]) - L(f, P_n, [a, b]) = (f(b) - f(a)) / N -> 0, $
  as $n -> infinity$, therefore $f$ is Riemann integrable on $[a, b]$.
]

#problem[
  Suppose $f_1, f_2, ... : [a, b] -> RR$ are Riemann integrable functions
  that converges uniformly to $f: [a, b] -> RR$. Prove that $f$ is Riemann
  integrable on $[a, b]$ and
  $
    integral_a^b f = lim_(n -> infinity) integral_a^b f_n.
  $
]

#solution[
  $f_n$ converging to $f$ uniformly means
  $ lim_(n -> infinity) sup_[a, b] |f - f_n| = 0 $

  Let $u_n = sup_[a, b] |f-f_n|$, then for any interval $[c, d] subset.eq [a,
  b]$, if $x_0$ is the value of $x in [c, d]$ such that $f (x_0) = sup_[c, d] f$,
  we must have:
  $
    abs(sup_[c, d] f - sup_[c, d] f_n) <= abs(f(x_0) - f_n (x_0)) + abs(f_n (x_0)
    - sup_[c, d] f_n) <= u_n + sup_[c, d] f - inf_[c, d] f
  $
  Then, for every partition $P$ of $[a, b]$ into $a = x_0 < x_1 < ... < x_n =
  b$, we have
  $
    abs(U(f, P, [a, b]) - U(f_n, P, [a, b])) &= abs(sum_(j = 1)^n (x_j -
    x_(j-1)) (sup_([x_(j - 1), x_j]) f_n - sup([x_(j - 1), x_j]) f)) \
    &<= sum_(j = 1)^n (x_j - x_(j-1)) (u_n + sup_[a, b] f - inf_[a, b] f) \
    &<= (b - a) u_n + (U(f_n, P, [a, b]) - L(f_n, P, [a, b])).
  $

  Similarly, we have:
  $
    abs(L(f, P, [a, b]) - L(f_n, P, [a, b])) <= (b - a) u_n + (U(f, P, [a,
          b]) - L(f, P, [a, b])).
  $

  Hence,
  $
    abs(U(f, P, [a, b]) - L(f, P, [a, b])) <= 2(b-a) u_n + 3(U(f_n, P, [a, b]) -
      L(f_n, P, [a, b])).
  $

  The right hand side expression can be made arbitrarily small by choosing $n$
  such that $u_n <= epsilon/(5(b-a))$ and $P$ such that $U(f_n, P, [a, b]) -
  L(f_n, P, [a, b]) <= epsilon/(5(b-a))$. QED.
]

== Part B

#problem[
  Define $f: [0, 1] -> RR$ as follows:
  $
    f(x) = cases(0 "if" x "is irrational", 1/n "if" x "is rational and"
  n "is the smallest positive integer"\ "   such that" x =  m/n "for some integer m")
  $
  Show that $f$ is Riemann integrable and compute $integral_0^1 f$.
]

#solution[
  It is trivial to see $L(f, [0, 1]) = 0$. Now it suffices to prove that $U(f,
  [0, 1]) = 0$.

  Consider the uniform partition $P$ that divides $[0, 1]$ into $n(n-1) + 2$
  equal subintervals. Then, since every rational number lies in at most 2
  subintervals, we must have the following:
  $
    U(f, P, [0, 1]) <= 2 / (n(n-1) + 2) sum_(k = 1)^(n(n-1) / 2+1) f(q_k),
  $
  where $q_1, q_2, ...$ is an enumeration of the rationals in $[0, 1]$,
  ordered by $f(q_1) < f(q_2) < ...$. In fact, by noting that $q_1 = 1, q_2 =
  1/2, q_3 = 1/3, q_4 = 2/3, ...$ (here, if $f(p) = f(q)$ then we fallback to
  default ordering to enumerate $p$ and $q$), it is possible to evaluate the sum as
  $ sum_(k = 1)^(n(n-1) / 2+1) f(q_k) = 1 + sum_(k = 2)^n (k - 1) / k <= n $

  Hence, $U(f, [0, 1]) <= U(f, P, [0, 1]) <= (2n)/(n(n-1) + 2) -> 0$ as $n ->
  infinity$. QED.
]

#problem[
  Suppose $f: [a, b] -> RR$ is a bounded function. Prove that if $f$ is Riemann
  integrable on $[a, b]$ if and only if
  $ L(-f, [a, b]) = -L(f, [a, b]) $
]

#solution[
  This is a direct consequence of the fact that $L(-f, [a, b]) = -U(f, [a,
  b])$ for all $f: [a, b] -> RR$.
]

#problem[
  Suppose $f, g: [a, b] -> RR$ are bounded functions. Prove that
  $ L(f, [a, b]) + L(g, [a, b]) <= L(f + g, [a, b]) $
  and
  $ U(f, [a, b]) + U(g, [a, b]) >= U(f + g, [a, b]) $
]

#solution[
  This is a direct consequence of the fact that
  $ inf_A f + inf_A g <= inf_A (f + g) "and" sup_A f + sup_A g >= sup_A (f + g) $
  for every $f: A -> RR$.
]

#problem[
  Give an example of bounded functions $f, g: [0, 1] -> RR$ such that
  $ L(f, [0, 1]) + L(g, [0, 1]) < L(f + g, [0, 1]) $
  and
  $ U(f, [0, 1]) + U(g, [0, 1]) > U(f + g, [0, 1]) $
]

#solution[
  Letting $f$ be the Dirichlet function:
  $ f = cases(1 "if" x "is rational", 0 "otherwise") $
  and $g = 1 - f$, then
  $ L(f, [0, 1]) + L(g, [0, 1]) = 0 < 1 = L(f + g, [0, 1]), $
  and
  $ U(f, [0, 1]) + U(g, [0, 1]) = 2 > 1 = U(f + g, [0, 1]). $
]

#problem[
  Give an example of a sequence of continuous real-valued functions $f_1, f_2,
  ...$ on $[0, 1]$ and a continuous real-valued function $f$ on $[0, 1]$ such
  that $ f(x) = lim_(n -> infinity) f_n (x) $ for each $x in [0, 1]$ but
  $ integral_0^1 f(x) != lim_(n -> infinity) integral_0^1 f_n (x). $
]

#solution[
  Let $r_n$ be some monotonically decreasing sequence that converges to $0$,
  and a sequence $x_n$ such that $[x_n-r_n, x_n+r_n] subset.eq [0, 1]$ for all
  $k = 1, 2, ...$ Then, define $f_n$ as
  $
    f_n (x) = cases(1/r_n - abs(x_n - x)/r_n^2 "if" x in [x_n - r_n, x_n + r_n],
  0 "otherwise"),
  $
  we have
  $
    integral_0^1 f_n = 2 - integral_(x_n - r_n)^(x_n) (x_n-x) / r_n^2 dif x -
    integral_(x_n)^(x_n + r_n) (x-x_n) / r_n^2 dif x = 1,
  $
  so $lim_(n -> infinity) integral_0^1 f_n = 1$.

  However, we can pick $r_n$ and $x_n$ such that $f(x) = lim_(n -> infinity) f_n
  (x) = 0$ for all $x in [0, 1]$. In order to do so, we need to have the
  following:

  $
    forall x in [0, 1], exists N in ZZ^+: x in.not (x_n - r_n, x_n + r_n),
    forall n > N
  $

  We will iteratively construct $x_n$ and $r_n$ as follows.

  1. Divides $[0, 1]$ into two equal subintervals $(0, 1/2)$ and $(1/2, 1)$.
    Then, let $(x_1 - r_1, x_1 + r_1) = (0, 1/2)$, i.e. $x_1 = 1/4$ and $r_1 = 1/4$.
  2. For every $x in [0, 1/2]$, we will let $N = 1$, which means that $(x_n
    - r_n, x_n + r_n) subset.eq (1/2, 1)$ for all $n > 1$. The idea is very
    simple: we just chop that interval into two subintervals again: $(x_2-r_2,
    x_2+r_2) = [1/2, 3/4]$, and $(x_n-r_n, x_n+r_n) subset.eq [3/4, 1]$ for
    all $n > 2$. Then, $x_2 = 5/8$ and $r_2 = 1/8$.
  3. Continue the steps above to infinity.

  More rigorously, we can define $x_n$ and $r_n$ explicitly as follows:
  $ r_n = 1 / 2^(n + 1) "and" x_n = 1 - 3 / 2^(n + 1). $

  Then, for every $x in [0, 1)$ ($x = 1$ does not lie on any $[x_n - r_n,
  x_n + r_n]$, so we can ignore this case), there exists some $N$ such that
  $ 1 / 2^N <= 1 - x < 1 / 2^(N - 1). $
  So if,
  $
    &x in (x_n - r_n, x_n + r_n) = (1 - 1 / 2^(n - 1), 1 - 1 / 2^n) \
    &=> (1 - 1 / 2^(N - 1), 1 - 1 / 2^N] sect (1 - 1 / 2^(n - 1), 1 - 1 / 2^n) !=
    emptyset \
    &=> N = n
  $

  Hence, for every $n > N$, $x$ can not belong to $(x_n - r_n, x_n + r_n)$,
  which is equivalent to $f_n (x) = 0, forall n > N$. Hence, $f(x) = 0$ for all
  $x in [0, 1]$, and therefore
  $ lim_(n -> infinity) integral_0^1 f_n = 1 != 0 = integral_0^1 f. $
]

= Measures

== Part A

#problem[
  Prove that if $A$ and $B$ are subsets of $RR$ and $|B| = 0$, then $|A union B|
  = |A|$.
] <zero-outer-measure>

#solution[
  This trivially holds since $|A union B| <= |A| + |B| = |A|$ and $A subset.eq A
  union B$.
]

#problem[
  Suppose $A subset.eq RR$ and $t in R$. Let $t A = {t a: a in A}$. Prove that
  $|t A| = |t| |A|$.
]

#solution[
  Every open interval cover $I_1, I_2, ...$ of $A$ has an one-to-one
  correspondence to $t I_1, t I_2, ...$ of $t A$. Since
  $ sum_(k = 1)^infinity ell(t I_k) = t sum_(k = 1)^infinity ell(I_k) $, it must
  hold that $|t A| = t |A| = |t| |A|$.
]

#problem[
  Prove that if $A, B subset.eq RR$ and $|A| < infinity$, then $|B without A| >=
  |B| - |A|$.
]

#solution[
  The inequality is equivalent to $|A| + |B without A| >= |B|$, which is clearly
  true due to subadditivity.
]

#problem[
  Suppose $F$ is a subset of $RR$ with the property that every open cover of $F$
  has a finite subcover. Prove that $F$ is closed and bounded.
]

#solution[
  Consider the following open cover of $RR$ (and therefore $F$):
  $ F subset.eq RR = union.big_(n in ZZ^+) (-n, n). $
  Since $F$ has a finite subcover, denoted $(-n_1, n_1), (-n_2, n_2), ...,
  (-n_k, n_k)$, it must be contained in $(-max_(i = 1, ..., k) n_i, max_(i = 1,
  ..., k) n_i)$. Hence, $F$ is bounded.

  Denote $d(x, y) = |x - y|$ as the distance between two real numbers $x$ and
  $y$#footnote[This is to make it so that this argument generalizes well to
  higher-dimensional spaces (and Hausdorff topological spaces in general)],
  $B(x, r) = (x-r, x+r)$ as the open ball centered at $x$ with radius $r$.

  Consider an arbitrary $x_0 in RR without F$, then
  $ cal(C) = {B(x, 1 / 2 d(x, x_0)) | x in C} $
  is an open cover of $F$. Hence, there exists finitely many $x_1, x_2, ...,
  x_n$ such that $ F subset.eq union.big_(k = 1)^n B(x_k, 1/2 d(x_k, x_0)). $

  Now, consider $ N = B(x_0, 1/2 min_(k = 1, 2, ...n) d(x_k, x_0)), $
  $N$ clearly does not intersect any of $B(x_k, 1/2 d(x_k, x_0))$, so $N$ does
  not contain any element in $F$, i.e. $N subset.eq RR without F$.

  Hence, $RR without F$ is open, i.e. $F$ is closed.
]

#problem[
  Suppose $A$ is a set of closed subsets of $RR$ such that $sect.big_(F in A) F
  = diameter$. Prove that if $A$ contains at least one bounded set, then there
  exist $n in ZZ^+$ and $F_1, ..., F_n in A$ such that $F_1 sect ... sect F_n =
  diameter$.
]

#solution[
  Let $A'$ be the set of closed and bounded sets in $A$ and pick any $B in A'$.
  This invokes the Axiom of Choice.

  We have $sect.big_(F in A without {B}) F sect B = diameter$, so
  $
    B subset.eq RR without sect.big_(F in A without {B}) F = union.big_(F in A
    without B) (RR without F).
  $

  Here, we have an open cover of closed and bounded $B$, so there must exists
  finitely many $F_1, F_2, ..., F_n$ such that

  $ B subset.eq union.big_(k = 1)^n (RR without F_k). $

  Letting $F_(n + 1) = B$, we have $F_1 sect ... sect F_(n + 1) = diameter$.
  QED.
]

#problem[
  Prove that if $a, b  in RR$ and $a < b$, then
  $ |(a, b)| = |[a, b)| = |(a, b]| = b - a. $
]

#solution[
  Use @zero-outer-measure.
]

#problem[
  Suppose $a, b, c, d$ are real numbers with $a < b$ and $c < d$. Prove that
  $|(a, b) union (c, d)| = b - a + d - c$ if and only if $(a, b) sect (c, d) =
  diameter$.
]

#solution[
  If $(a, b) sect (c, d) = diameter$, then WLOG assuming $a < b < c < d$, and
  then $ |(a, b)| + |(c, d)| >= |(a, b) union (c, d)| >= |(a, d) without (b,
  c)|, $ and equivalently
  $ b - a + d - c >= |(a, b) union (c, d)| >= d - a - c + b. $
  This means $|(a, b) union (c, d)| = b - a + d - c$.

  Now, if $|(a, b) union (c, d)| = b - a + d - c = |(a, b)| + |(c, d)|$, then we
  must have $|(a, b) sect (c, d)| = 0$. The intersection of two open interval
  is either empty, or another open interval (with non-zero outer measure).
  Hence, it must be the case that $(a, b) sect (c, d) = diameter$.
]

#problem[
  Prove that if $A subset.eq RR$ and $t > 0$ then $|A| = |A sect (-t, t)| + |A
  sect (RR without (-t, t))|$.
]

#solution[
  For every open interval $I = (c, d)$,
  - $(c, d) sect (-t, t)$ is an open interval $(max{c, -t}, min{d, t})$. Denote
    this interval as $alpha(I)$.
  - For every $epsilon > 0$,
    $
      (c, d) sect (RR without (-t, t)) &= ((c, d) sect (-infinity, -t]) union ((c,
          d) sect [t, infinity))\
      &subset.eq ((c, d) sect (-infinity, -t)) union ((c,
          d) sect (t, infinity)) union {-t, t}\
      &subset.eq (c, min{d, -t}) union (max{c, t}, d) union {-t, t}.
    $
    Denote $beta(I) = (c, min{d, -t})$ and $ gamma(I) = (max{c, t}, d)$.

  It is trivial to see that $ell(I) = ell(alpha(I)) + ell(beta(I)) +
  ell(gamma(I))$, and if $I_1, I_2, ...$ is an open interval cover of $A$, the
  following are covers of $A sect (-t, t)$ and $A sect (RR without (-t, t))$
  respectively:
  - $S = {alpha(I_1), alpha(I_2), ...}$ of $A sect (-t, t)$.
  - $T = {(t-epsilon, t+epsilon), (-t-epsilon, -t+epsilon), beta(I_1), beta(I_2),
  ..., gamma(I_1), gamma(I_2), ...}$ of $A sect (RR without (-t, t))$.

  We have:
  $
    sum_(n=1)^infinity ell(I_n) &= (sum_(n=1)^infinity ell(alpha(I_n))) +
    (sum_(n=1)^infinity ell(beta(I_n, epsilon)) + sum_(n=1)^infinity
      ell(gamma(I_n, epsilon))) \
    &= sum_(I in S) ell(I) + sum_(I in T) ell(I) - 4 epsilon \
    &>= |A sect (-t, t)| + |A sect (RR without (-t, t))| - 4epsilon.
  $

  Letting $epsilon -> 0$ and taking the infimum of left hand side, it must be
  the case that $|A| >= |A sect (-t, t)| + |A sect (RR without (-t, t))|$.
  Combining this with subadditivity yields the desired result.
]

#problem[
  Prove that $|A| = lim_(t -> infinity) |A sect (-t, t)|$ for all $A subset.eq
  RR$.
] <outer-measure-limit>

#solution[
  We consider the following two cases:

  - If $|A| < +infinity$, then the equality is equivalent to $lim_(t ->
    infinity) |A without (-t, t)| = 0$. This limit definitely exists and is
    non-negative due to the fact that $f(t) = |A without (-t, t)|$ is decreasing
    and non-negative.

    Assuming that this limit is positive, i.e. there exists some $epsilon, t_0 > 0$
    such that $forall t > t_0, |A without (-t, t)| > epsilon$. This is equivalent to
    the fact that if $I_1, I_2, ...$ is an open interval cover of $A without (-t,
    t)$, then $sum_(k = 1)^infinity ell(I_k) > epsilon$.

    Furthermore, if this series converges to some $S < +infinity$, then there
    exists some $k_0$ such that $sum_(k=1)^k_0 ell(I_k) > L - epsilon$ and
    therefore $sum_(k=k_0+1)^infinity ell(I_k) < epsilon$. If we take

    $ t' = max{t, max_(1 <= k <= k_0) (max {-inf I_k, sup I_k})}, $

    then $I_(k_0+1), I_(k_0+2), ...$ is an open interval cover of $A without (-t',
    t')$, but $sum_(k=k_0+1)^infinity ell(I_k) < epsilon$, a contradiction. Hence,
    it must be the case that $sum_(k=1)^infinity ell(I_k) = +infinity$.

    However, this means that $|A|$ must be equal to $+infinity$, a
    contradiction.

  - If $|A| = +infinity$, then we have to prove $lim_(t -> infinity) |A sect
    (-t, t)| = +infinity$. This limit exists due to monotonicity, so we assume
    the limit is finite, i.e. there exists some $M > 0$ such that $M > |A sect
    (-t, t)|$ for all $t in RR$.

    #lemma[
      If $I_1, I_2, ...$ is an open interval partition of $RR without C$, where
      $C$ is a countable set, then for all $A subset.eq RR$, $ |A| = sum_(k =
      1)^infinity |A sect I_k|. $
    ] <outer-measure-lemma>

    #proof[
      We trivially have $|A| <= sum_(k = 1)^infinity |A sect I_k|$ due to
      subadditivity. Consider an arbitrary open interval cover $J_1, J_2, ...$
      of $A$, then for every $k in NN$, $J_1 sect I_k, J_2 sect I_k, ...$ is an
      interval of $A sect I_k$, so it must be the case that

      $ |A sect I_k| <= sum_(j = 1)^infinity ell(J_j sect I_k). $

      Hence,

      $
        sum_(k = 1)^infinity |A sect I_k| <= sum_(k = 1)^infinity sum_(j =
        1)^infinity ell(J_j sect I_k) = sum_(j = 1)^infinity ell(J_j),
      $

      where the last equality holds due to the fact that $I_1, I_2, ...$ is a
      partition of $RR without C$.

      However, by the definition of the outer measure, $sum_(j = 1)^infinity
      ell(J_j) <= |A|$, so equality must hold: $|A| = sum_(k = 1)^infinity |A
      sect I_k|$.
    ]

    Now, consider the following open interval partition of $RR without ZZ$:
    $ (0, 1), (-1, 0), (1, 2), (-2, -1), ..., $
    i.e. $I_k = (pi(k), pi(k) + 1)$, where $pi$ denotes some bijection from
    $NN$ to $ZZ$.

    Then, we have $|A sect (-t, t)| = sum_(k in ZZ) |A sect (k, k + 1) sect (-t,
    t)|$. Hence, $ lim_(t -> infinity) |A sect (-t, t)| = lim_(t -> infinity)
    sum_(k in ZZ) |A sect (k, k + 1) sect (-t, t)| < M. $

    However, for every $t in ZZ$, we have:

    $
      sum_(k in ZZ) |A sect (k, k + 1) sect (-t, t)| = sum_(k = -t)^(t - 1) |A
      sect (k, k + 1)|.
    $

    So,

    $ sum_(k = -infinity)^infinity |A sect (k, k + 1)| < M. $

    Applying the lemma again, we have $|A| = sum_(k = -infinity)^infinity |A
    sect (k, k + 1)|$. Hence, $|A| < M$, a contradiction with $|A| = +infinity$.
]

#problem[
  Prove that $|[0,1]without QQ| = 1$.
]

#solution[
  We have $|[0,1] without QQ| <= |[0, 1]| = 1$ and $|[0,1] without QQ| + |[0,1]
  sect QQ| >= [0, 1] = 1$. Since $[0, 1] sect QQ$ is countable, it has outer
  measure zero. From this it becomes trivial that $|[0,1] without QQ| = 1$.
]

#problem[
  Prove that if $I_1, I_2, ...$ is a disjoint sequence of open intervals, then:
  $ abs(union.big_(k=1)^infinity I_k) = sum_(k=1)^infinity ell(I_k). $
]

#solution[
  See @outer-measure-lemma.
]

#problem[
  Suppose $r_1, r_2, ...$ is a sequence that contains every rational number. Let
  $ F = RR without union.big_(k = 1)^infinity (r_k - 1 / 2^k, r_k + 1 / 2^k). $

  + Show that $F$ is a closed subset of $RR$.
  + Prove that if $I$ is an interval contained in $F$, then $I$ contains at most
    one element.
  + Prove that $|F| = infinity$.
] <closed-rational-complement>

#solution[
  + The complement of $F$ is the union of countably many open intervals, so it
    must be open. By definition, $F$ is closed.
  + If $I$ is an interval containing at least two elements, then it must contain
    a rational number. But since the complement of $F$ contains all rational
    numbers, $I$ must not be fully contained in $F$, a contradiction.
  + From subadditivity, we have
    $
      |RR without F| <= sum_(k = 1)^infinity ell((r_k - 1/2^k, r_k + 1/2^k)) +
      sum_(k = 1)^infinity 1 / 2^(k-1) = 1.
    $
    Hence it must be the case that $|F| = +infinity$.
]

#problem[
  Suppose $epsilon > 0$. Prove that there exists a subset $F$ of $[0, 1]$ such
  that $F$ is closed, every element of $F$ is an irrational number, and $|F| > 1
  - epsilon$.
]

#solution[
  Let $r_1, r_2, ...$ be an enumeration of $QQ sect [0, 1]$.

  Then, denote
  $
    F = [0, 1] without union.big_(k = 1)^infinity (r_k - epsilon / 2^k, r_k +
      epsilon / 2^k),
  $
  and proceed as in @closed-rational-complement.
]

#problem[
  See MIRA.
]

#solution[
  https://www.youtube.com/shorts/6aDB9VLnyZQ
]

== Measurable Spaces and Functions

#let Sc = math.cal([S])

#problem[
  Show that $Sc = {union_(n in K) (n, n + 1] : K subset.eq ZZ}$ is a
  $sigma$-algebra on $RR$.
]

#solution[
  Denote $S(K) = union_(n in K) (n, n + 1]$. It is clear that
  - $diameter = S(diameter) in Sc$.
  - $S(K) = RR without S(ZZ without K)$.
  - $union.big_(k = 1)^infinity S(K_k) = S(union.big_(k = 1)^infinity K_k)$.

  From this it should be trivial to verify $Sc$ is a $sigma$-algebra.
]

#problem[
  Verify the bullet points in Example 2.28 (MIRA).
]

#solution[
  Trivial
]

#problem[
  Suppose $Sc$ is the smallest $sigma$-algebra on $RR$ containing ${(r, s]: r, s
  in QQ}$. Prove that $Sc$ is the collection of Borel subsets of $RR$.
]

#solution[
  #lemma[
    Suppose $Sc$ is the smallest $sigma$-algebra on $RR$ containing ${(r,
    infinity): r in QQ}$. Prove that $Sc$ is the collection of Borel subsets of $RR$.
    This result also holds if $(r, infinity)$ is replaced by $[r, infinity)$.
  ] <common-sigma>

  #proof[
    We know that $(a, infinity): a in RR$ generates the Borel sets, so it
    suffices to represent $(a, infinity)$ by $(q, infinity): q in QQ$.

    Let $q_1, q_2, ...$ be an enumeration of $QQ sect (-infinity, a)$, then
    $ [a, infinity) = sect.big_(k = 1)^infinity (q_k, infinity). $

    Let $q'_1, q'_2, ...$ be an enumeration of $QQ sect (a, infinity)$, then
    $ (a, infinity) = union.big_(k = 0)^infinity [q'_k, infinity]. $
  ]

  Using @common-sigma, for every $a in QQ$, we can write
  $ (a, infinity) = union.big_(k = 0)^infinity (a + k, a + k + 1]. $
]

#problem[
  Suppose $Sc$ is the smallest $sigma$-algebra on $RR$ containing ${(r, n]: r in
  QQ, n in ZZ}$. Prove that $Sc$ is the collection of Borel subsets of $RR$.
]

#solution[
  Using @common-sigma, for every $a in QQ$, we can write
  $
    (a, infinity) = (a, ceil(a) + 1] union union.big_(k = 1)^infinity (ceil(a) +
      k, ceil(a) + k + 1].
  $
]

#problem[
  Suppose $Sc$ is the smallest $sigma$-algebra on $RR$ containing ${(r, r+1): r in
  QQ}$. Prove that $Sc$ is the collection of Borel subsets of $RR$.
]

#solution[
  Using @common-sigma, for every $a in QQ$, we can write
  $ (a, infinity) = union.big_(k = 0)^infinity (a + k, a + k + 1]. $
]

#problem[
  Suppose $Sc$ is the smallest $sigma$-algebra on $RR$ containing ${[r,
  infinity): r, s in QQ}$. Prove that $Sc$ is the collection of Borel subsets of
  $RR$.
]

#solution[
  This is easily a consequence of @common-sigma.
]

#problem[
  Prove that the collection of Borel subsets of $RR$ is translation invariant.
  More precisely, prove that if $B subset.eq RR$ is a Borel set and $t in RR$,
  then $t + B$ is a Borel set.
] <borel-transl-invar>

#solution[
  Let $Sc = {B subset.eq RR: t + B "is a Borel set"}$. Then $Sc$ is a
  $sigma$-algebra on $RR$:
  - $diameter in Sc$ since $t + diameter = diameter$ is a Borel set.
  - If $S in Sc$, then $(t + RR) without (t + S) = t + (R without S)$ is a Borel
    set, so $R without S in Sc$.
  - If $S_1, S_2, ... in Sc$, then $union.big_(k = 1)^infinity (t + S_k) = t +
    union.big_(k = 1)^infinity S_k$ is a Borel set, so $union.big_(k = 1)^infinity
    S_k in Sc$.

  Since open sets are translation invariant, $Sc$ must contain all open sets,
  so it must be a superset of $cal(T)$, the collection of all Borel sets.
]

#problem[
  Prove that the collection of Borel subsets of $RR$ is dilation invariant.
  More precisely, prove that if $B subset.eq RR$ is a Borel set and $t in RR$,
  then $t B$ is a Borel set.
]

#solution[
  Similar to @borel-transl-invar.
]

#problem[
  Give an example of a measurable space $(X, Sc)$ and a function $f: X -> RR$
  such that $|f|$ is $Sc$-measurable but $f$ is not $Sc$-measurable.
]

#solution[
  $ f(x) = cases(1 "if" x in E, 0 "otherwise"), $
  for any non-measurable subset $E$ of $X$.
]

#problem[
  Show that the set of real numbers that have a decimal expansion with the digit
  5 appearing infinitely often is a Borel set.
]

#solution[
  We will construct this set step-by-step.

  The set of reals with decimal expansion having the digit $5$ appearing right
  after the decimal place is,

  $ S(1) = union.big_(k in ZZ) [k + 0.5, k + 0.6]. $

  Here, for simplicity, we consider $0.6 = 0.59999...$ to be a part of $S(1)$.

  Then, this result can be trivially generalized: the set of reals with decimal
  expansion having the digit $5$ appearing at the $k$-th position after the
  decimal place is $S(k) = 10^(-k) S(1)$.

  Now, if $r$ is a real number with finitely many 5's in its decimal expansion,
  then there exists some natural number $N$ such that $r in.not S(k)$ for all $k
  > N$. Hence, the set of all such $r$ must be,

  $ T = union.big_(N in NN) (RR without union.big_(k > N) S(k)). $

  The complement of $T$ is the set we need to construct: the set of real numbers
  that have a decimal expansion with the digit 5 appearing infinitely often.

  Now, looking back at our construction, we can see that we only use the
  complement and (countably infinite) union operation, so the complement of $T$
  in $RR$ is a Borel set.
]

#let Tc = math.cal([T])
#let Yc = math.cal([Y])
#problem[
  Suppose $Tc$ is a $sigma$-algebra on a set $Yc$ and $X in Tc$. Let $Sc = {E in
  Tc : E subset.eq X}$.
  + Show that $Sc = {F sect X: F in Tc}$.
  + Show that $Sc$ is a $sigma$-algebra on $X$.
]

#solution[
  + Denote $Sc' = {F sect X: F in Tc}$. If $E in Sc$, then $E = E sect X in
    Sc'$. If $E' = F sect X in Sc$ for some $F in Tc$, then $F sect X$ must also
    be in $Tc$, so $E' in Sc$. Hence $Sc = Sc'$.
  + Verifying:
    - $diameter in Sc$ since $diameter sect X = diameter$, $diameter in Tc$.
    - If $E in Sc$, then $X without E in Tc$ and $X without E subset.eq X$, so
      $X without E in Sc$.
    - If $E_1, E_2, ... in Sc$, and $E = union.big_(k = 1)^infinity E_k$, then
      $E subset.eq X$ and $E in Tc$, so $E in Sc$.
]

#problem[
  Suppose $f: RR -> RR$ is a function.
  + For $k in ZZ^+$, let
    $
      G_k = {a in RR: "there exists" delta > 0 "such that" |f(b) - f(c)| < 1 / k
        "for all" b, c in (a - delta, a + delta)}.
    $
    Prove that $G_k$ is an open subset of $RR$ for each $k in ZZ^+$.
  + Prove that the set of points at which $f$ is continuous equals $sect.big_(k
    = 1)^infinity G_k$.
  + Conclude that the set of points at which $f$ is continuous is a Borel set.
]

#solution[
  + The predicate $P(K): $ "$|f(b) - f(c)| < 1/k, forall b, c in K$" can be
    trivially seen to be "monotonically decreasing", i.e. if $A subset.eq B$, then
    $P(B) => P(A)$. Hence, if $a in G_k$, i.e. there exists an open neighborhood
    $N$ of $a$ such that $P(N)$ holds, then for every $a' in N$, we can
    construct a neighborhood $N'$ of $a'$ that is completely enclosed by $N$, so
    $P(N')$ must also hold. Hence, $a' in G_k$. From this, we can conclude that
    $G_k$ is open.
  + By definition.
  + That set is the intersection of countably many open sets, so it must be a
    Borel set itself.
]

#problem[
  Suppose $(X, Sc)$ is a measurable space, $E_1, E_2, ..., E_n$ are disjoint
  subsets of $X$, and $c_1, c_2, ..., c_n$ are distinct nonzero real numbers.
  PRove that $c_1 chi_E_1 + c_2 chi_E_2 + ... + c_n chi_E_n$ is an
  $Sc$-measurable if and only if $E_1, E_2, ..., E_n in Sc$.
]

#solution[
  This trivially holds since $f^(-1)({c_k}) = E_k$ for all $k = 1, 2, ..., n$.
]

#problem[
  + Suppose $f_1, f_2, ...$ is a sequence of functions from a set $X$ to $RR$.
    Explain why
    $
      {x in X: "the sequence" f_1(x), f_2(x), ... "has a limit on" RR}\
      = sect.big_(n = 1)^infinity union.big_(j = 1)^infinity sect.big_(k =
      j)^infinity (f_j - f_k)^(-1) ((-1 / n, 1 / n)).
    $
  + Suppose $(X, Sc)$ is a measurable space and $f_1, f_2, ...$ is a sequence of
    $Sc$-measurable functions from $X$ to $RR$. Prove that
    $ {x in X: "the sequence" f_1(x), f_2(x), ... "has a limit on" RR} $
    is an $Sc$-measurable subset of $X$.
]

#solution[
  + $f_1(x), f_2(x), ...$ is convergent if and only if for any $epsilon > 0$,
    there exists some $j in NN$ such that $|f_s (x) - f_k (x)| < epsilon$ holds
    for all $s, k >= j$. We can set $s = j$ by using the triangle inequality.

    Discretize $epsilon$ as $1/n$ as $n -> infinity$, we arrive at the desired
    result.
  + Trivial.
]

#problem[
  Suppose $X$ is a set and $E_1, E_2, ...$ is a disjoint sequence of subsets of
  $X$ such that $union.big_(k = 1)^infinity E_k = X$. Let $Sc = {union_(k in K)
  E_k : K subset.eq ZZ^+}$.

  + Show that $Sc$ is a $sigma$-algebra on $X$.
  + Prove that a function from $X$ to $RR$ is $Sc$-measurable if and only if the
    function is constant on $E_k$ for every $k in ZZ^+$.
]

#solution[
  + Trivial.
  + If $f(x) != f(y)$, $x, y in E_1$ (without loss of generality), then consider
    $T = f^(-1)({f(x)})$. We have $x in T, y in.not T$, but if $T = union.big_(k
    in K) E_k in Sc$, we can see that both $1 in K$ and $1 in.not K$ hold, a
    contradiction. The other way is trivial.
]

#problem[
  Suppose $Sc$ is a $sigma$-algebra on a set $X$ and $A subset.eq X$. Let
  $Sc_A = {E in Sc: A subset.eq E "or" A sect E = diameter}.$

  + Prove that $Sc_A$ is a $sigma$-algebra on $X$.
  + Suppose $f: X -> RR$ is a function. Prove that $f$ is measurable with
    respect to $Sc_A$ is and only if $f$ is measurable with respect to $Sc$ and
    $f$ is constant on $A$.
]

#solution[
  + Verifying:
    - $diameter = A sect diameter in Sc_A$.
    - If $E in Sc_A$, then either:
      - $A subset.eq E in Sc$, then $(X without E) sect A = diameter$ and $X
        without E in Sc$, or
      - $A sect E = diameter$, then $A subset.eq X without E$ and $X without E
        in Sc$.
      In both cases, we can conclude that $X without E in Sc_A$.
    - If $E_1, E_2, ... in Sc_A$, and $E = union.big_(k = 1)^infinity E_k in Sc$, and
      either:
      - Some $E_k$ is a superset of $A$, so $A subset.eq E$, or
      - $E_k sect A = diameter$ for all $k$, so $E sect A = diameter$.
      In both cases, we can conclude that $E in Sc_A$.
  + Two ways:
    - If $f$ is measurable with respect to $Sc_A$, then for all Borel set $B$,
      $f^(-1)(B) in Sc_A subset.eq Sc$, so $f$ is measurable with respect to
      $Sc$. Furthermore, if $f(x) != f(y)$ for some $x, y in A$, then
      $f^(-1)({f(x)})$ contains $x$ and not $y$. Such a set could not be in
      $Sc_A$, a contradiction.
    - If $f$ is measurable with respect to $Sc$ and $f$ is constant on $A$ (so
      $f(A)$ is a singleton set), then for every Borel set $B$, we have two
      cases:
      - $f(A) subset.eq B$, so $f^(-1)(B)$ contains $A$ and therefore is included
        in $Sc_A$.
      - $f(A) sect B = diameter$, so $f^(-1) sect A = diameter$ and therefore is
        included in $Sc_A$.
]

#problem[
  Suppose $X$ is a Borel subset of $RR$ and $f: X -> RR$ is a function such that
  ${x in X: f "is not continuous at" x}$ is a countable set. Prove $f$ is a
  Borel measurable function.
]

#solution[
  Denote $D = {x in X: f "is not continuous at" x}$.

  For every $a in RR$, we can write $f^(-1)((a, infinity))$ as
  $ f^(-1)((a, infinity)) = D'(a) union E, $
  where
  $ D'(a) = {x in D: f(x) > a} subset.eq D, $
  and
  $ E = {x in X without D: f(x) > a}. $

  Since $D$ is countable, any subset $D'(a)$ of it must be a Borel set.
  Furthermore, we can easily prove that $E$ is an open set due to the property
  of continuous functions, so $f^(-1)((a, infinity))$ is a Borel set.
]

#problem[
  Suppose $f: RR -> RR$ is differentiable at every element of $RR$. Prove that
  $f'$ is a Borel measurable function from $RR$ to $RR$.
]

#solution[
  $f'$ is the limit of the functions $f_1, f_2, ...$ defined as:
  $ f_k (x) = (f(x + 1 / k) - f(x)) / (1 / k), $
  which are all clearly Borel measurable ($f$ being differentiable implies that
  $f$ is continuous, therefore Borel measurable).
]

#problem[
  Suppose $X$ is a nonempty set and $Sc$ is the $sigma$-algebra on $X$
  consisting of all subsets of $X$ that are either countable or have a countable
  complement on $X$. Give a characterization of the $Sc$-measurable real-valued
  functions on $X$.
]

#solution[
  #lemma[
    A uncountable subset $S$ of $RR$ can always be partitioned into two
    uncountable subsets $A$ and $B$ such that $sup A <= inf B$.
  ]

  #proof[
    Define $M = {x in R : S sect (-infinity, x) "is countable" }$ and $N =
    {x in R : S sect (x, infinity) "is countable" }$.

    If $M sect N$ has some element $u$, then $S subset.eq (S sect (-infinity, u)) union
    (S sect (u, infinity)) union {u}$ must be countable, a contradiction.
    However, it can be proven that $m = sup M in M$ by writing

    $
      S sect (-infinity, m) = union.big_(k = 1)^infinity (S sect (-infinity, m -
          1 / k)),
    $
    where we can be sure that $m - epsilon in S$ for all $epsilon > 0$.

    The right-hand-side expression is the countable union of countable sets, so
    $S sect (-infinity, m)$ must be countable as well. Similarly, we can prove
    that $n = inf N in N$.

    Now, if $m < n$, then we can pick $r = (m + n)/2 in RR without M without N$,
    and define $A = S sect (-infinity, r)$, $B = S sect [r, infinity)$.

    Otherwise, if $m >= n$, then $M sect N$ is nonempty, a contradiction.
  ]

  Using the lemma, we can see that if $f(X)$ is uncountable, we can partition it
  into two uncountable subsets $A$ and $B$. Then, $f^(-1)(A)$ and $f^(-1)(B)$
  are both uncountable, so $f$ is not measurable, a contradiction.

  Hence, $f(X)$ must be countable, i.e. there exists a partition $X_1, X_2, ...
  $ of $X$ such that $f(X_i) = {y_i}$ are singletons and $y_i != y_j$ for all $i
  != j$.

  Since $f^(-1)({y_i}) = X_i$, all $X_i$ must be countable or have a countable
  complement (cocountable). If there are two cocountable sets $X_1$ and $X_2$
  (without loss of generality, and we assume $y_1 < y_2$ here),
  then $f^(-1)((-infinity, (y_1+y_2)/2)) supset.eq X_1$ and
  $f^(-1)(((y_1+y_2)/2, infinity)) supset.eq X_2$, which are both uncountable,
  so none of the preimages can be in the $Sc$. Hence,

  $ f "is non-constant on a countable set." $

  We can trivially verify that all $f$ satisfying the above property is
  $Sc$-measurable.
]

#problem[
  Suppose $(X, Sc)$ is a measurable space and $f, g: X -> RR$ are
  $Sc$-measurable functions. Prove that if $f(x) > 0$ for all $x in X$, then
  $f^g$ (which is the function whose value at $x in X$ equals $f(x)^(g(x))$) is
  an $Sc$-measurable function.
]

#solution[
  We have $f(x)^(g(x)) = exp(g(x) dot ln f(x))$.
]

#problem[
  Prove 2.52 (MIRA)
]

#solution[
  We have:
  $ f^(-1)({infinity}) = sect.big_(n = 1)^infinity f^(-1)((n, infinity]) in Sc, $
  and
  $
    f^(-1)((a, infinity)) = f^(-1)((a, infinity]) without f^(-1)({infinity})
    in Sc.
  $ <normal-borel>

  Hence, for every Borel subset $B$ of $[-infinity, infinity]$:
  - If $infinity in.not B$, then $f^(-1)(B) in Sc$ due to @normal-borel and
    Theorem 2.39 of MIRA.
  - Otherwise, $f^(-1)(B) = f^(-1)(B without {infinity}) union
    f^(-1)({infinity})$, the union of two $Sc$-measurable sets.
]

#problem[
  Suppose $B subset.eq RR$ and $f: B -> RR$ is an increasing function. Prove
  that $f$ is continuous at every element of $B$ except for a countable subset
  of $B$.
] <countable-discont-inc>

#solution[
  Define a mapping $mu$ as follows:

  Since $f$ is increasing, for every $x_0 in B$, there exists left and right
  limits:
  $
    f^+(x) = lim_(x -> x_0^+) f(x) = inf f((x, +infinity)), f^-(x) = lim_(x ->
    x_0^-) f(x) = sup f((-infinity, x)).
  $

  $f$ is discontinuous at $x$ if and only if $f^+(x) > f^-(x)$. Then, there
  exists rationals $q$ in $(f^-(x), f^+(x))$. For each such $q$, we define
  $mu(q) = x$.

  For every unmarked $q$, we let $mu(q)$ be some undefined value, e.g.
  $diameter$. We can be sure that a rational $q$ is never marked twice, since
  the intervals $(f^-(x), f^+(x))$ does not intersect. Then, $mu$ is an
  surjective#footnote[This statement might not be true if there is no $q$ that
  maps to $diameter$ but this is just a small and easily fixable detail.]
  mapping from $QQ$ to $D union {diameter}$, where $D$ is the set of
  discontinuities of $f$.

  Hence, it must be the case that $D$ is countable.
]

#problem[
  Suppose $f: RR -> RR$ is a strictly increasing function. Prove that the
  inverse function $f^(-1): f(RR) -> RR$ is a continous function.
]

#solution[
  - If $f^(-)(x) = f^(+)(x) = f(x)$, then $f^(-1)$ is trivially continous at
  $f(x)$.
  - Otherwise, we have $f^(-)(x) <= f(x) <= f^(+)(x)$, and either:
    - $f^(-)(x) < f(x) = f^(+)(x)$, or
    - $f^(-)(x) = f(x) < f^(+)(x)$, or
    - $f^(-)(x) < f(x) < f^(+)(x)$.
    The only difference between the three cases is the neighborhood of $f(x)$ in
    $f(RR)$. In the first and second case, it is a interval with $f(x)$ being
    one of its endpoint, while the third case yields a singleton neighborhood.
]

#problem[
  Suppose $f: RR -> RR$ is a strictly increasing function and $B subset.eq RR$
  is a Borel set. Prove that $f(B)$ is a Borel set.
]

#solution[
  Let $Sc = {B subset.eq RR: f(B) "is a Borel set"}$. Proving $Sc$ is a
  $sigma$-algebra containing all open sets reduces to proving the following:

  #lemma[If $E subset.eq RR$ is open, than $f(E)$ is a Borel set.]

  #proof[
    $E$ can be written as the disjoint union of countably many open intervals
    $I_k$, so this effectively reduces the problem to the case where $E = (a,
    b)$ for some $a, b in RR$.

    Denote $Y = RR without f((a, b))$. Define an equivalent relation $tilde$ as
    $x tilde y <==> [x, y] subset.eq Y$. Then, the equivalent classes $C_alpha$,
    $alpha in A$ must be disjoint intervals. If some interval $C_alpha = {y}$ is
    degenerate (a singleton), then there are sequences $a_n$ and $b_n$ such
    that:
    - $f(a_n)$ is strictly increasing and have a upper bound of $y$.
    - $f(b_n)$ is strictly decreasing and have a upper bound of $y$.

    Since $f$ is strictly increasing, $a_n$ and $b_n$ are monotonic sequences
    ($a_n$ strictly increasing, $b_n$ strictly decreasing), and therefore they
    both converges at some $u = lim a_n$ and $v = lim b_n$. Then, $f(u) >= y >=
    f(v)$, so it must be the case that $u = v$ and $f(u) = y$, which contradicts
    $y in RR without f((a, b))$.

    Hence, $Y$ can be partitioned into disjoint non-degenerate intervals, and
    using the rational number trick, we can prove that the number of those
    intervals must be countably infinite at most, so $Y$ turns out to be a Borel
    set. Hence, $f((a, b))$ is also a Borel set.
  ]
]

#problem[
  Suppose $B subset.eq RR$ and $f: B -> RR$ is an increasing function. Prove
  that there exists a sequence $f_1, f_2, ...$ of strictly increasing function
  from $B$ to $RR$ such that
  $ f(x) = lim_(k -> infinity) f_k (x) $
  for every $x in B$.
]

#solution[
  One such example is $f_k (x) = f(x) + x / k$.
]

#problem[
  Suppose $B subset.eq RR$ and $f: B -> RR$ is a bounded increasing function.
  Prove that there exists an increasing function $g: RR -> RR$ such that $g(x) =
  f(x)$ for all $x in B$.
]

#solution[
  $ g(x) = inf_(x' in [x, +infinity)) f(x'), " or" M "if no such" x' "exists", $
  where $M$ is an upper bound of $f(x), x in B$.
]

#problem[
  Prove or give a counterexample: If $(X, Sc)$ is a measurable space and $f: X
  -> [-infinity, infinity]$ is a function such that $f^(-1)((a, infinity)) in S$
  for every $a in RR$, then $f$ is a $Sc$-measurable function.
]

#solution[
  $ f(x) = cases(infinity "if" x in E, -infinity "otherwise"), $
  where $E$ is a non-$Sc$-measurable subset of $X$.
]

#problem[
  Suppose $f: B -> RR$ is a Borel measurable function. Define $g: RR -> RR$ by
  $ g(x) = cases(f(x) "if" x in B, 0 "if" x in RR without B) $
  Prove that $g$ is a Borel measurable function.
]

#solution[
  $
    g^(-1)((a, infinity)) = cases(f^(-1)((a, infinity)) "if" a >= 0, f^(-1)((a,
  infinity)) sect B "otherwise").
  $
]

#problem[
  Give an example of a measurable space $(X, Sc)$ and a family ${f_t}_(t in
  RR)$ such that each $f_t$ is an $Sc$-measurable function from $X$ to $[0, 1]$,
  but the function $f: X -> [0, 1]$ defined by
  $ f(x) = sup {f_t (x): t in RR} $
  is not $Sc$-measurable.
]

#solution[
  Let $E$ be a non-Borel subset of $RR$. Define $f_t$ as
  $ f_t (x) = cases(1 "if" x = t "and" t in E, 0 "otherwise"), $
  then every $f_t$ is a Borel measurable function, but $f = chi_E$ is not.
]

#problem[
  Show that
  $
    lim_(j -> infinity) (lim_(k -> infinity) (cos (j!pi x))^(2k)) = cases(1 "if"
    x "is rational", 0 "if" x "is irrational").
  $
]

#solution[
  If $x = p/q$ is a rational number, then $cos(j!pi x)^(2k) = 1$ for all
  $j > q$.

  If $x$ is irrational, then $|cos(j!pi x)| < 1$ for all $j$. Hence, $(cos (j!
  pi x))^(2k) -> 0$ as $k -> infinity$, so the limit is $0$.
]

== Measures and Their Properties

#problem[
  Explain why there does not exists a measure space $(X, Sc, mu)$ with the
  property that ${mu(E): E in Sc} = [0, 1)$
]

#solution[
  $Sc$ always have a maximal set $X$, so $mu(X) = max {mu(E): E in Sc}$, but
  $[0, 1)$ does not have a maximum, so contradiction.
]

*Let $2^(ZZ^+)$ denote the $sigma$-algebra on $ZZ^+$ consisting of all subsets of $ZZ^+$*

#problem[
  Suppose $mu$ is a measure on $(ZZ^+, 2^ZZ^+)$. Prove that there is a sequence
  $w_1, w_2, ...$ in $[0, infinity]$ such that
  $ mu(E) = sum_(k in E) w_k $
  for every set $E subset.eq ZZ^+$.
]

#solution[
  $ w_k = mu({k}). $
]

#problem[
  Give an example of a measure $mu$ on $(ZZ^+, 2^ZZ^+)$ such that
  $ {mu(E): E subset ZZ^+} = [0, 1]. $
]

#solution[
  $mu$ defined as
  $ mu({k}) = 1 / 2^k. $
]

#problem[
  Give an example of a measure $mu$ on $(ZZ^+, 2^ZZ^+)$ such that
  $
    {mu(E): E subset ZZ^+} = {infinity} union union.big_(k = 0)^infinity [3k,
      3k+1].
  $
]

#solution[
  $mu$ defined as
  $ mu({k}) = cases(1/2^t "if" k = 2t, 3 "if" k = 2t + 1), ("here" t in ZZ). $
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space such that $mu(X) < infinity$. Prove
  that if $cal(A)$ is a set of disjoint sets in $Sc$ such that $mu(A) > 0$ for
  every $A in cal(A)$, then $cal(A)$ is a countable set.
]

#solution[
  This is a direct consequence of the fact that $sum_(r in U) f(r) < infinity$
  for some $f: U -> (0, infinity)$ can only hold when $U$ is countable.

  The infinite sum is defined as
  $
    sum_(r in U) f(r) = sup_(U' subset.eq U\
    U' "countable") sum_(r in U') f(r).
  $

  Consider the set $U(epsilon) = {r in U: f(r) > epsilon}$. If there exists some
  $epsilon > 0$ such that $U(epsilon)$ is infinite, then

  $ sum_(r in U) f(r) >= sum_(r in U'') f(r) = infinity, $
  where $U''$ is some countably infinite subset of $U(epsilon)$, which
  contradicts with the convergent of the infinite sum.

  Hence, the following set must be countably infinite at most.
  $ U' = union.big_(n in ZZ^+) U(1 / n), $
  but we can trivially see that $U = U'$. Hence, $U$ must be countable.

  Returning to the problem, we can see that
  $
    infinity > mu(X) >= mu(union.big_(A in cal(A)) A) = sum_(A in cal(A)) mu(A) >
    0,
  $
  which means that $cal(A)$ must be countable.
]

#problem[
  Find all $c in [3, infinity)$ such that there exists a measurable space $(X,
  Sc, mu)$ with
  $ {mu(E): E in Sc} = [0, 1] union [3, c] $.
]

#solution[
  Denote $I = [0, 1] union [3, c]$. Since $I$ is bounded, we can trivially see
  that $I$ must be symmetric, i.e. $I = c - I$. This can only hold when $c = 4$.

  For an example, consider the space $X = [0, 1] union {infinity}$, $Sc$ is the
  set of all Borel sets, and $mu$ defined as:

  $
    mu(A) = |A without {infinity}| + cases(3 "if" infinity in A, 0 "otherwise").
  $
]

#problem[
  Give an example of a measurable space $(X, Sc, mu)$ such that
  $ {mu(E): E in Sc} = [0, 1] union [3, infinity] $.
]

#solution[
  Let $q_1, q_2, ...$ be an enumeration of the rationals. Define
  $ mu(A) = |A without QQ| + sum_(q_i in A) (i + 2). $
]

#problem[
  Give an example of a set $X$, a $sigma$-algebra $Sc$ of subsets of $X$, a set
  $cal(A)$ of subsets of $X$ such that the smallest $sigma$-algebra on $X$
  containing $cal(A)$ is $Sc$, and two measures $mu$ and $nu$ on $(X, Sc)$ such
  that $mu(A) = nu(A)$ for all $A in cal(A)$ and $mu(X) = nu(X) < infinity$, but
  $mu != nu$.
]

#solution[
  $X = RR$, $Sc$ is the set of all Borel subsets of $RR$, $cal(A) = {(a,
  +infinity) : a in RR}$. Now, we can define a class of measure $mu$ by scaling
  the outer measure with an arbitrary constant $t > 0$, but $mu(A) = infinity$
  for all $A in cal(A)$.
]

#problem[
  Suppose $mu$ and $nu$ are measures on a measurable space $(X, Sc)$ Prove that
  $mu + nu$ is a measure on $(X, Sc)$. \[Here $mu + nu$ is the usual sum of two
  functions: if $E in Sc$ then $(mu + nu)(E) = mu(E) + nu(E)$.\]
]

#solution[
  Trivial.
]

#problem[
  Give an example of a measure space $(X, Sc, mu)$ and a decreasing sequence
  $E_1 supset.eq E_2 supset.eq ...$ of sets in $Sc$ such that
  $ mu(sect.big_(k = 1)^infinity E_k) != lim_(k -> infinity) mu(E_k). $
]

#solution[
  Consider the outer measure on the Borel subsets of $RR$ and
  $ E_k = (k, infinity). $
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space and $C, D, E in Sc$ such that
  $mu(C sect D) < infinity, mu(C sect E) < infinity, mu(D sect E) < infinity.$
  Find and proe a formula for $mu(C union D union E)$ in terms of $mu(C), mu(D),
  mu(E), mu(C sect D), mu(C sect E), mu(D sect E),$ and $mu(C sect D sect E)$.
]

#solution[
  The proof is similar to the inclusion–exclusion formula.
  $
    mu(C union D union E) = mu(C) + mu(D) + mu(E) - mu(C sect D) - mu(C sect E) -
    mu(D sect E) \ + mu(C sect D sect E).
  $
]

#problem[
  Suppose $X$ is a set and $Sc$ is the $sigma$-algebra of all subsets $E$ of $X$
  such that $E$ is countable or $X without E$ is countable. Give a complete
  description of the set of all measures on $(X, Sc)$.
]

#solution[
  - If $X$ is countable, then $mu$ is uniquely determined by the values
    $mu({x})$ of all $x in X$.
  - Otherwise, it needs an additional value of $mu(X)$, which must be at least
    $
      sum_(x in X) mu({x}) = sup_(X' subset X\
      X' "countable") sum_(x in X') mu({x}).
    $

    Note that the infinite sum on the left-hand-side is not a countable sum, and
    therefore it does not equal $mu(X)$.
]

== Lebesgue Measure

#problem[
  + Show that the set consisting of those numbers in $(0, 1)$ that have a
    decimal expansion containing one hundred consecutive 4s is a Borel subset of
    $RR$.
  + What is the Lebesgue measure of this set?
]

#solution[
  + This set $S$ can be written as
    $
      union.big_(n = 0)^infinity 10^(-n) [0.underbrace(444..44, 100 "digits"),
        0.underbrace(444..4, 99 "digits")5]
    $
  + Consider another set $T$ consisting of all numbers in $[0, 1]$ that have a
    digit with value $underbrace(444..44, 100 "digits")$ in its decimal
    expansion. This set can be easily seen as a subset of $S$.

    #lemma[
      Let $b$ be a positive number larger than 2 and $d$ be a digit in base-$b$
      ($0 <= d <= b - 1$). Then, the set of all numbers in $(0, 1)$ that have a
      decimal expansion containing the digit $d$ (after the decimal point) has
      Lebesgue measure $1$.
    ]

    #proof[
      Let $S_n$ be the set of all positive numbers in $(0, 1)$ that have a
      decimal expansion not containing the digit $d$ in the first $n$-th
      position after the decimal point.

      Chop up $(0, 1)$ into $b^n$ equal intervals with the same $n$ digits after
      the decimal point, and by a simple counting argument, $(b-1)^n$ of these
      intervals does not contain the digit $d$ in the first $n$-th positions.
      Hence, $|S_n| = (b-1)^n/b^n = (1 - 1/b)^n$.

      Since our set is the complement of $S$, the intersection of all $S_n$, it
      must have a Lebesgue measure of at least $1 - (1 - 1/b)^n$ for all $n >
      0$. Letting $n$ approach infinity, we acquire the desired result.
    ]

    Since $S$ has a subset with Lebesgue measure 1 and itself is a subset of
    another set ($(0, 1)$) with Lebesgue measure 1, $S$ must have Lebesgue
    measure 1.
]

#problem[
  Prove that there exists a bounded set $A subset.eq RR$ such that $|F| <= |A| -
  1$ for every closed set $F subset.eq A$.
]

#solution[
  Let $A$ be any bounded non-Lebesgue-measurable set. Then there exists some
  $epsilon_0$ such that for every closed set $F subset.eq A$, $|A without F| >=
  epsilon_0$. Since $F$ is closed, $|A| = |F| + |A without F| <= |F| +
  epsilon_0$.

  Hence, $|F| <= |A| - epsilon_0$. We can turn the $epsilon_0$ into an 1 by
  simply scaling $A$ by a factor of $1/epsilon_0$.
]

#problem[
  Prove that there exists a set $A subset.eq RR$ such that $|G without A| =
  infinity$ for every open set $G$ that contains $A$.
]

#solution[
  Once again, let $V$ be any bounded non-Lebesgue-measurable set. Assuming $V$
  is bounded in $(0, 1)$, and there exists some $epsilon > 0$ such that $|G
  without V| > epsilon$ for all open supersets $G$ of $V$.

  Then, consider the set $A = union.big_(n in ZZ) (V + n)$. Any open
  superset $G$ of $A$ can be divided up into multiple $G_k = G sect (k, k + 1)
  supset.eq V + k, k in ZZ$
  that does not intersect any of $V + n$ with $k != n$. Hence, we can see
  that $G_k$ is an open set that contains $V + k$, so it must hold that:
  $ |G_k without (V + k)| >= epsilon. $

  Finally, we have
  $
    |G without A| = abs(union.big_(n in ZZ) (G_k without (V + k)))
    >= infinity dot epsilon = infinity.
  $

  Here, we get around the subadditivity problem by considering that $G_k without
  (V + k) = (G without A) sect (k, k + 1)$ for every $k$, and additivity follows
  from the result of @outer-measure-lemma.
]

#problem[
  The phrase _nontrivial interval_ is used to denote an interval of $RR$ that
  contains more than one element. Recall that an interval might be open, closed,
  or neither.

  + Prove that the union of each collection of nontrivial intervals of $RR$ is
    the union of a countable subset of that collection.
  + Prove that the union of each collection of nontrivial intervals of $RR$ is a
    Borel set.
  + Prove that there exists a collection of closed intervals of $RR$ whose union
    is not a Borel set.
]

#solution[
  + Let $S = union.big_(I in cal(C)) I$ be such a set, where $cal(C)$ is a
    collection of nontrivial intervals.

    #let int(x) = [Int #x]
    Denote $int(X)$ as the interior of the set $X$, then we know that there
    exists some countable $cal(C') subset.eq cal(C)$ such that
    $ S' = union.big_(I in cal(C)) int(I) = union.big_(I in cal(C')) int(I), $
    from Theorem 0.59 of the MIRA supplement.

    Hence, our concern shifts to the boundary of the intervals in $cal(C)$.
    Without loss of generality, we will consider the right endpoints $x in S
    without S'$. Then, there has to be some $(alpha, x] in cal(C)$ or $[alpha, x] in
    cal(C)$ for some $alpha$ (the left endpoint and whether $alpha$ is contained
    in this range does not matter). We can get over the axiom of choice by
    imposing some sort of total ordering on the set $cal(C)$. Denote this
    interval as $I(x)$.

    Now, we can prove that $int(I(x)) sect int(I(y)) = diameter$ for all $x, y in S
    without S', x != y$. Otherwise, then without loss of generality, assuming
    that $int(I(x)) = (alpha, x), I(y) = (beta, y), x < y$, it must be the case that
    $beta < x < y$, so $x in int(I(y)) subset.eq S'$, a contradiction.

    Since $int(I(x))$'es are pairwise disjoint, we can establish a mapping from
    a subset of the rationals to ${int(I(x)): x in S without S'}$. Hence, the
    number of elements in $S without S'$ must be countable at most.

    Here, the argument does not change if we factor the left endpoints of
    intervals, since union of finitely many countable sets remains countable.
  + Trivial.
  + $union.big_(x in S) [x, x] = S$ for some non-Borel $S$.
]

#problem[
  Prove that if $A subset.eq RR$ is Lebesgue measurable, then there exists an
  increasing sequence $F_1 subset.eq F_2 subset.eq ...$ of closed sets contained
  in $A$ such that
  $ abs(A without union.big_(k = 1)^infinity F_k) = 0. $
]

#solution[
  Direct result of Theorem 2.71, taking $F_k = union.big_(n = 1)^k F'_k$, where
  $F'_k$ are sets found from the theorem.
]

#problem[
  Suppose $A subset.eq RR$ and $|A| < infinity$. Prove that $A$ is Lebesgue
  measurable if and only if for every $epsilon > 0$ there exists a set $G$ that
  is the union of finitely many disjoint bounded open intervals such that $|A
  without G| + |G without A| < epsilon$.
]

#solution[
  Let $A$ be a Lebesgue measurable set.

  From @outer-measure-limit, there exists some $t > 0$ such that $|A without
  (-t, t)| < epsilon/3$.

  Since $A$ is Lebesgue measurable, there exists open superset $E$ of $A$ such
  that $|E without A| < epsilon/3$. Hence,

  By Theorem 0.59 of the MIRA supplement, we can write
  $E sect (-t, t)$ as the disjoint union of countably many open intervals $I_k
  subset.eq (-t, t)$, $k = 1, 2,
  ...$ Then, $|E| = sum_(k = 1)^infinity |I_k|$, there exists some $K > 0$ such that
  $sum_(k = K + 1)^infinity |I_k| < epsilon/3$.

  Define $G = union.big_(k = 1)^K I_k$, then we have $G subset.eq (-t, t)$ and
  therefore
  $
    |A without G| &= |(A without G) sect (-t, t)| + |(A without G) without (-t,
      t)|\
    &<= |(E without G) sect (-t, t)| + |A without (-t, t)|\
    &<= |(E sect (-t, t)) without G| + |A without (-t, t)|\
    &<= abs(union.big_(k = K + 1)^infinity I_k) + |A without (-t, t)|\
    &< (2epsilon) / 3,
  $
  and
  $
    |G without A| <= |E without A| < epsilon / 3.
  $
  Hence,
  $ |A without G| + |G without A| < epsilon. $

  The other direction is trivial.
]

#problem[
  Prove that if $A subset.eq RR$ is Lebesgue measurable, then there exists a
  decreasing sequence $G_1 subset.eq G_2 subset.eq ...$ of open sets containing
  $A$ such that
  $ abs((sect.big_(k = 1)^infinity G_k) without A) = 0. $
]

#solution[
  Direct result of Theorem 2.71, taking $G_k = sect.big_(n = 1)^k G'_k$, where
  $G'_k$ are sets found from the theorem.
]

#problem[
  Prove that the collection of Lebesgue measurable subsets of $RR$ is
  translation invariant. More precisely, prove that if $A subset.eq RR$ is
  Lebesgue measurable and $t in RR$, then $A + x$ is Lebesgue measurable.
]

#solution[
  This is a direct consequence of Theorem 2.71 and the translation invariance of
  outer measure.
]

#problem[
  Prove that the collection of Lebesgue measurable subsets of $RR$ is
  dilation invariant. More precisely, prove that if $A subset.eq RR$ is
  Lebesgue measurable and $t > 0$, then $t A$ is Lebesgue measurable.
]

#solution[
  This is a direct consequence of Theorem 2.71 and the dilation invariance of
  outer measure.
]

#problem[
  Prove that if $A$ and $B$ are disjoint subsets of $RR$ and $B$ is Lebesgue
  measurable, then $|A union B| = |A| + |B|$.
]

#solution[
  Let $B' subset.eq B$ be a Borel set such that $|B without B'| = 0$. Then,
  from $|B'| = |B'| + |B without B'| >= |B| >= |B'|$, we have
  $|A union B| >= |A union B'| = |A| + |B'| = |A| + |B|$.
]

#problem[
  Prove that if $A subset.eq RR$ and $|A| > 0$, then there exists a subset of
  $A$ that is not Lebesgue measurable.
]

#solution[
  Assuming otherwise. Consider the Vitali set $V subset.eq [0, 1]$.
  Then, $ A = union_(q in QQ) (A sect (q + V)). $
  From our assumption, all $A sect (q + V)$ must be Lebesgue measurable and has
  measure zero. But this means $|A| = 0$, a contradiction.
]

#problem[
  Suppose $b < c$ and $A subset.eq (b, c)$. Prove that $A$ is Lebesgue
  measurable if and only if $|A| + |(b, c) without A| = c - b$.
]

#solution[
  Assuming that $|A| + |(b, c) without A| = c - b$.

  #lemma[
    If $B$ is a Borel set and $A subset.eq B$, then there exists some Borel set
    $C$ such that $|A| = |C|$ and $A subset.eq C subset.eq B$.
  ]

  #proof[
    For every $epsilon > 0$, there exists some open interval cover
    $cal(C)(epsilon)$ such that
    $ abs(sum_(I in cal(C) (epsilon)) ell(I)) <= |A| + epsilon, $
    where $I in cal(C)$ are open intervals that cover $A$.

    Then, we can define $C$ as
    $ C = B sect sect.big_(n = 1)^infinity cal(C) (1 / n). $

    And we must have $|A| <= |C| <= |A| + 1/n$ for all $n in ZZ^+$. This trivially
    implies that $|C| = |A|$.
  ]

  Let $B$ be a Borel set such that $|A| = |B|$ and $A subset.eq B subset.eq (b,
  c)$. Then, we have $|(b, c) without E| = |(b, c) without A|$.

  Let $B'$ be a Borel set such that $|(b, c) without A| = |B'|$ and $(b, c)
  without A subset.eq B'$. Then, similarly, $|A| = |(b, c) without B'|$.

  Hence, $|A| = |B| = |(b, c) without B'|$ and $(b, c) without B' subset.eq A
  subset.eq B$. This means $|A without ((b, c) without B')| <= |B without ((b,
  c) without B')| = |B| - |(b, c) without B'| = 0$. By Theorem 2.71, $A$ must be
  Lebesgue measurable.

  The other direction is trivial.
]

#problem[
  Suppose $A subset.eq RR$. Prove that $A$ is Lebesgue measurable if and only if
  $ |(-n, n) sect A| + |(-n, n) without A| = 2n $
  for every $n in ZZ^+$.
]

#proof[
  From the previous problem, we know that $(-n, n) sect A$ is Lebesgue
  measurable for all $n in ZZ^+$. Hence,
  $ A = union.big_(n = 1)^infinity ((-n, n) sect A) $
  must also be Lebesgue measurable as well.
]

#problem[
  Show that $1/4$ and $9/13$ are both in the Cantor set.
]

#proof[
  $1/4 = 0.overline(02)_(3)$ and $9/13 = 0.overline(200)_(3)$.
]

#problem[
  Show that $13/17$ is not in the Cantor set.
]

#proof[
  $13/17 = 0.202bold(1)..._(3)$.
]

#problem[
  List the eight open intervals whose union is $G_4$ in the definition of the
  Cantor set.
]

#solution[
  Trivial (I'm not doing this).
]

#problem[
  Let $C$ denote the Cantor set. Prove that ${1/2 x + 1/2 y: x, y in C} = [0, 1]$.
]

#solution[
  For every number $z = 0.z_1 z_2 ..._(3)$, we can construct $x = 0.x_1
  x_2..._(3)$ and $y = 0.y_1 y_2 ..._(3)$ such that $z = 1/2 x + 1/2 y$ as
  follows:

  - If $z_k = 0$, then $x_k = y_k = 0$.
  - If $z_k = 2$, then $x_k = y_k = 2$.
  - If $z_k = 1$, then $x_k = 0$ and $y_k = 2$.

  Then, we can see that $z_k = 1/2 (x_k + y_k)$ and $x_k, y_k in {0, 2}$ for all
  $k > 0$. Hence $x, y in C$.
]

#problem[
  Prove that every open interval of $RR$ contains either infinitely many or no
  elements in the Cantor set.
]

#solution[
  Assume the open interval $I$ contains some $x in C$. Since $I$ is open, there
  exists a neighborhood of $x$ that is in $I$, which means that there exists
  some $N$ that we can freely tweak the values in the $n$ digits of $x$'s
  base-$3$ expansion and still end up with some value $b' in I$. Now, the
  problem becomes trivial. In fact, we can easily define a mapping from $[0, 1]$
  to $I$ by replacing substituting the digits in the binary representation of $x
  in [0, 1]$ to the digits in the binary representation of $b$ from the $N$-th
  onwards.
]

#problem[
  Evaluate $integral_0^1 Lambda$, where $Lambda$ is the Cantor function.
]

#solution[
  By the definition of $Lambda$, we have
  $ Lambda(1 - x) = 1 - Lambda(x). $

  Then, since $Lambda$ is Riemann integrable due to continuity, we have

  $
    integral_0^1 Lambda(x) dif x = integral_0^1 Lambda(1-x) dif x = 1 / 2
    integral_0^1 (Lambda(x) + Lambda(1-x)) = 1 / 2
  $
]

#problem[
  Evaluate each of the following:
  + $Lambda(9/13)$.
  + $Lambda(0.93)$.
]

#solution[
  + $Lambda(9/13) = Lambda(0.overline(200)_(3)) = 0.overline(100)_(2) = 4 / 7.$
  + $Lambda(0.93) = Lambda(0.221..._(3)) = 0.111_(2) = 7 / 8.$
]

#problem[
  Find each of the following sets:
  + $Lambda^(-1)({1/3})$;
  + $Lambda^(-1)({5/16})$.
]

#solution[
  Trivial (no it's not I'm just lazy).
]

#problem[
  + Suppose $x$ is a rational number in $[0, 1]$. Explain why $Lambda(x)$ is
    rational.
  + Suppose $x in C$ is such that $Lambda(x)$ is rational. Explain why $x$ is
    rational.
]

#solution[
  + The base-2 (or 3) representation of a rational number is either finite or
    periodic. The $Lambda$ function clearly preserves this property.
  + Since $x in C$, the $Lambda$ function does no trimming. If $Lambda(x)$ has a
    finite base-2 representation, then clearly $x$ must have a finite base-3
    representation. Otherwise, the base-2 representation of $Lambda(x)$ is
    periodic and infinite, and so does the base-3 representation of $x$.
]

#problem[
  Show that there exists a function $f: RR -> RR$ such that the image under $f$
  of every nonempty open interval is $RR$.
]

#solution[
  See https://en.wikipedia.org/wiki/Conway_base_13_function.
]

#problem[
  For $A subset.eq RR$, the quantity
  $ sup{|F|: F "is a closed bounded subset of" RR "and" F subset.eq A} $
  is called the _inner measure_ of $A$.

  + Show that if $A$ is a Lebesgue measurable subset of $RR$, then the inner
    measure of $A$ equals the outer measure of $A$.
  + Show that inner measure is not a measure on the $sigma$-algebra of all
    subsets of $RR$.
]

#solution[
  + If $A$ is Lebesgue measurable, then there exists closed subsets $F_1, F_2,
    ... subset.eq A$ such that $lim_(n -> infinity) |A without F| = 0$.
    Equivalently, $lim_(n -> infinity) |F| = |A|$, hence the inner measure of
    $A$ is at least $|A|$.

    Now, assuming that this quantity is somehow greater than $|A|$, which
    implies the existence of some subset $F subset.eq A$ with $|F| > |A|$. This
    clearly is a contradiction.
  + Basically the same reason as why the outer measure is not a measure in this
    measurable space.
]

== Convergence of Measurable Functions

#problem[
  Suppose $X$ is a finite set. Explain why a sequence of functions from $X$ to
  $RR$ converges pointwise on $X$ also converges uniformly on $X$.
] <uniconv-finite>

#solution[
  We have
  $
    lim_(n -> infinity) sup_(x in X) |f_n (x) - f(x)|
    = max_(x in X) lim_(n -> infinity) |f_n (x) - f(x)| = 0,
  $
  for all convergent $f_n -> f$ on $X$.
]

#problem[
  Give an example of a sequence of functions from $ZZ^+$ to $RR$ that converges
  pointwise on $ZZ^+$ but does not converge uniformly on $ZZ^+$.
]

#solution[
  $f_n (x) = x/n$.
]

#problem[
  Give an example of a sequence of continuous function $f_1, f_2, ...$ from $[0,
  1]$ to $RR$ that converges pointwise to a function $f: [0, 1] -> RR$ that is
  not a bounded function.
]

#solution[
  $f_n (x) = (n x)/(n x^2 + 2)$.
]

#problem[
  Prove or give a counterexample: If $A subset.eq RR$ and $f_1, f_2, ...$ is a
  sequence of uniformly continuous functions from $A$ to $RR$ that converges
  uniformly to a function $f: A -> RR$, then $f$ is uniformly continuous on $A$.
]

#solution[
  For any $n$, we have:
  $
    0 <= &limsup_(delta -> 0^+) sup_(d(x, y) < delta) |f(x) - f(y)|\
    <= &liminf_(n -> infinity) limsup_(delta -> 0^+) sup_(d(x, y) < delta)
    (|f(x) - f_n (x)| + |f(y) - f_n (y)| + |f_n (x) - f_n (y)|)\
    <= &liminf_(n -> infinity) limsup_(delta -> 0^+) sup_(d(x, y) < delta)
    (2 sup_(z in A) |f(z) - f_n (z)| + |f_n (x) - f_n (y)|)\
    <= &2 liminf_(n -> infinity) sup_(z in A) |f(z) - f_n (z)| + limsup_(n ->
    infinity) liminf_(delta -> 0^+) sup_(d(x, y) < delta) |f_n (x) - f_n (y)|\
    = &0.
  $
]

#problem[
  Give an example to show that Egorov's Theorem can fail without the hypothesis
  that $mu(X) < infinity$.
]

#solution[
  $f_n = chi_[n, n + 1]$ converges pointwise to $f = 0$.
  If this convergence is not uniform on some $E$, then if $E$ is unbounded
  (necessary if we want $|RR without E|$ to be finite), i.e. there exists a
  infinite unbounded sequence $x_1, x_2, ... in E$, then we can always find
  some $f_floor(x_k)$ that gives counterexamples to uniform continuity.
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space $mu(X) < infinity$. Suppose $f_1,
  f_2, ...$ is a sequence of $Sc$-measurable functions from $X$ to $RR$ such
  that $lim_(k -> infinity) f_k (x) = infinity$ for each $x in X$. Prove that
  for every $epsilon > 0$, there exists a set $E in Sc$ such that $mu(X without
  E) < epsilon$ and $f_1, f_2, ...$ converges uniformly to $infinity$ on $E$
  (meaning that for every $t > 0$, there exists $n in ZZ^+$ such that $f_k (x) >
  t$ for all integers $k >= n$ and all $x in E$).
]

#solution[
  Define $A_n (M) = f_n^(-1) ((M, infinity))$. Clearly $A_n (M)$ is increasing
  (with respect to $n$) and
  $ X = union.big_(n = 1)^infinity A_n (M). $
  Hence, $mu(X) = lim_(n -> infinity) mu(A_n (M))$. For any $epsilon > 0$,
  there exists $N(M, epsilon)$ such that $mu(X without A_n (M)) < epsilon$ for
  all $n >= N(M, epsilon)$. Define $S(M, epsilon) = A_N(M, epsilon) (M)$.

  Define
  $ E = sect.big_(n = 1)^infinity S(n, epsilon / 2^n), $
  then $ mu(X without E) <= sum_(n = 1)^infinity mu(X without S(n, epsilon/2^n))
  < epsilon. $

  For any $t > 0$, if $x in E$ then $x in S(ceil(t), epsilon/2^ceil(t))$, which
  means $x in A_k (M)$ for all $k > N(ceil(t), epsilon/2^ceil(t))$. Hence $f_n$
  converges uniformly to $f$ on $E$.
]

#problem[
  Suppose $F$ is a closed bounded subset of $RR$ and $g_1, g_2, ...$ is an
  increasing sequence of continuous real-valued functions on $F$ (thus $g_1 (x)
  <= g_2 (x) <= ...$ for all $x in F$) such that $sup{g_1 (x), g_2 (x), ...} <
  infinity$ for each $x in F$. Define a real-valued function $g$ on $F$ by
  $ g(x) = lim_(k -> infinity) g_k (x). $
  Prove that $g$ is continuous on $F$ if and only if $g_1, g_2, ...$ converges
  uniformly on $F$ to $g$.
]

#solution[
  Proving continuity of $g$ from uniform convergence is trivial.

  Assuming $g$ is continuous, so is $h_n = g - g_n$, then define
  $ E_n = h_n^(-1) ([0, epsilon)), $
  for some fixed $epsilon > 0$.

  Then, $F = union.big_(n = 1)^infinity E_n$. By the Heine-Borel theorem, there
  must exist a finite $S subset.eq ZZ^+$ such that $F = union.big_(n in S) E_n =
  E_(max S)$.

  Hence, $h_n (x) < epsilon, forall n > max S, x in F$.
]

#problem[
  Suppose $mu$ is the measure on $(ZZ^+, 2^ZZ^+)$ defined by
  $ mu(E) = sum_(n in E) 1 / 2^n. $
  Prove that for every $epsilon > 0$, there exists a set $E subset.eq ZZ^+$ with
  $mu(ZZ^+ without E) < epsilon$ such that $f_1, f_2, ...$ converges uniformly
  on $E$ for every sequence of functions $f_1, f_2, ...$ from $ZZ^+$ to $RR$
  that converges pointwise on $ZZ^+$.
]

#solution[
  Let $E = {1, 2, ..., M}$ such that $mu(ZZ^+ without E) < epsilon$, then this
  trivially follows from @uniconv-finite.
]

#problem[
  Suppose $F_1, ..., F_n$ are disjoint closed subsets of $RR$. Prove that if
  $ g: F_1 union ... union F_n -> RR $
  is a function such that $g|_F_k$ is a continuous function for each $k in {1,
  ..., n}$, then $g$ is a continuous function.
]

#solution[
  For every $x in F = union.big_(k = 1)^n F_k$, if $x in F_1$, then we can see
  that there is a neighborhood of $x$ that does not intersect any $F_k$ ($k >=
  2$).

  The existence of such a neighborhood is trivial. Since $x in RR without F_k$,
  an open set, there must be a neighborhood $N_k$ of $x$ that does not intersect
  $F_k$. Taking the (finite) intersection of all such neighborhoods yield the
  desired set.

  Denote this neighborhood as $N$, then since $N sect F = N sect F_1$, the
  continuity of $g|_F_1$ at $x$ trivially implies that of $g$ as well.
]

#problem[
  Suppose $F subset.eq RR$ such that every continuous function from $F$ to $RR$
  can be extended to a continuous function from $RR$ to $RR$. Prove that $F$ is
  a closed subset of $RR$.
]

#solution[
  If $F$ is not closed, then there exists a sequence $alpha_n in F$ that converges
  to some $alpha in.not F$. Let $f(x) = 1/abs(x - alpha)$ for $x in F$, then if
  $f$ can be extended to a continuous function $tilde(f)$, then:
  $
    tilde(f)(alpha) = lim_(x -> alpha) tilde(f)(x) = lim_(n -> infinity)
    1 / abs(alpha - alpha_n) = infinity.
  $
  This is impossible.
]

#problem[
  Prove or give a counterexample: If $F subset.eq RR$ is such that every bounded
  continuous function from $F$ to $RR$ can be extended to a continuous function
  from $RR$ to $RR$, then $F$ is a closed subset of $RR$.
]

#solution[
  Again, consider the function $f(x) = sin 1/abs(x - alpha)$, with $alpha$ being
  an element in $"cl" F without F$. This function is continuous on $F$, but
  is not on $RR$, as the limit $lim_(n -> infinity) sin 1/abs(alpha_n - alpha)$
  does not exist.
]

#problem[
  Give an example of a Borel measurable function $f$ from $RR$ to $RR$ such that
  there does not exist a set $B subset.eq RR$ such that $|RR without B| = 0$ and
  $f|_B$ is a continuous function on $B$.
]

#solution[
  See https://en.wikipedia.org/wiki/Smith%E2%80%93Volterra%E2%80%93Cantor_set
]

#problem[
  Prove or give a counterexample: If $f_t: RR -> RR$ is a Borel measurable
  function for each $t in RR$ and $f: RR -> (-infinity, infinity]$ is defined
  by:
  $ f(x) = sup {f_t (x): t in RR}, $
  then $f$ is a Borel measurable function.
]

#solution[
  For a non-Borel set $E$, if we let $f_t (x) = chi_(E sect {t})$, then $f =
  chi_E$ is non-Borel measurable.
]

#problem[
  Suppose $b_1, b_2, ...$ is a sequence of real numbers. Define $f: RR -> [0,
  infinity]$ by
  $
    f(x) = cases(sum_(k = 1)^infinity 1/(4^k |x - b_k|) "if" x in.not {b_1, b_2,
    ...}., infinity "if" x in {b_1, b_2, ...}.)
  $
  Prove that $|{x in RR: f(x) < 1}| = infinity$.
] <prob-borel-fn>

#proof[
  Consider the set
  $ A = union.big_(k = 1)^infinity [b_k - 1 / 2^k, b_k + 1 / 2^k], $
  then for every $x in RR without A$, we have:
  $
    f (x) = sum_(k = 1)^infinity 1 / (4^k |x - b_k|) < sum_(k = 1)^infinity 1 / 2^k = 1.
  $
  Clearly $|A| <= sum_(k = 1)^infinity 1/2^(k + 1) = 2$, so $|RR without A| = infinity$.
]

#problem[
  Suppose $B$ is a Borel set and $f: B -> RR$ is a Lebesgue measurable function.
  Show that there exists a Borel measurable function $g: B -> RR$ such that
  $ |{x in B: g(x) != f(x)}| = 0. $
]

#solution[
  Define $tilde(f): RR -> RR$ by
  $ tilde(f) (x) = cases(f(x) "if" x in B, 0 "otherwise"). $
  Then, for every Lebesgue measurable set $X$, we have
  $
    tilde(f)^(-1) (X) = cases(f^(-1)(X) union (RR without B) "if" 0 in B,
  f^(-1)(X) "otherwise").
  $
  Hence, $tilde(f)$ is Lebesgue measurable. Hence, there exists some $g: B ->
  RR$ such that
  $ |{x in RR: tilde(g)(x) != tilde(f)(x)}| = 0. $
  Take $g = tilde(g)|_B$, then clearly $g$ is Borel measurable, and
  $ |{x in B: g(x) != f(x)}| <= |{x in RR: tilde(g)(x) != tilde(f)(x)}| = 0$.
]

= Integration

== Integration with Respect to a Measure

#problem[
  Suppose $(X, Sc, mu)$ is a measure space and $f: X -> [0, infinity]$ is an
  $Sc$-measurable function such that $integral f dif mu < infinity$. Explain why
  $ inf_(x in E) f(x) = 0 $
  for each set $E in Sc$ with $mu(E) = infinity$.
]

#solution[
  Clearly if $inf_(x in E) f(x) > 0$, then
  $ integral f dif mu >= mu(E) inf_(x in E) f(x) = infinity, $ which is a contradiction.
]

#problem[
  Suppose $X$ is a set, $Sc$ is a $sigma$-algebra on $X$, and $c in X$. Define
  the Dirac measure $delta_c$ on $(X, Sc)$ by
  $ delta_c (E) = cases(1 "if" c in E, 0 "otherwise"). $
  Prove that if $f: X -> [0, infinity]$ is $Sc$-measurable, then $integral f
  dif delta_c = f(c)$.
]

#solution[
  For every $Sc$-partition $P$ of $X$ into $A_1, ..., A_m$, we have
  $
    cal(L)(f, P) = sum_(i = 1)^m mu(A_i) inf_(x in A_i) f(x) = sum_(A_i = {c})
    mu(A_i) f(c) <= mu({c}) f(c) = f(c).
  $
  Equality holds when $P$ is the partition ${c}, X without {c}$. Hence, $integral
  f dif delta_c = f(c)$.
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space and $f: X -> [0, infinity]$ is an
  $Sc$-measurable function. Prove that
  $ integral f dif mu > 0 <==> mu({x in X: f(x) > 0}) > 0. $
]

#solution[
  The converse is true. Now, if $integral f dif mu > 0$, then there exists a
  partition $A_1, ..., A_m$ with positive lower Lebesgue sum:
  $ sum_(i = 1)^m mu(A_i) inf_(x in A_i) f(x) > 0. $

  This means that there exists some $A_i$ with positive measure and $inf_(x in
  A_i) f(x) > 0$. Hence, $mu({x in X: f(x) > 0}) >= mu(A_i) > 0$.
]

#problem[
  Give an example of a Borel measurable function $f: [0, 1] -> (0, infinity)$
  such that $L(f, [0, 1]) = 0$.
]

#solution[
  Let $f$ be
  $ f(x) = cases(1/n "if" x = m/n in QQ, 1 "otherwise"), $
  We can prove that
  $ inf_(x in A) f(x) = 0, $
  for every non-degenerate interval $A subset.eq [0, 1]$, hence the result.
]

#problem[
  Verify the assertion that integration with respect to counting measure is
  summation.
]

#solution[
  Trivial.
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space, $f: X -> [0, infinity]$ is
  $Sc$-measurable, and $P$ and $P'$ are $Sc$-partitions of $X$ such that
  each set in $P$ is a subset of some set in $P'$. Prove that
  $ cal(L)(f, P) <= cal(L)(f, P'). $
]

#solution[
  Trivial (literally no difference from the equivalent result for lower Riemann
  sums).
]

#problem[
  Suppose $X$ is a set, $Sc$ is the $sigma$-algebra on $X$, and $w: X -> [0,
  infinity]$ is a function. Define a measure $mu$ on $(X, Sc)$ by
  $ mu(E) = sum_(x in E) w(x) $
  for $E subset.eq X$. Prove that if $f: X -> [0, infinity]$ is a function, then
  $ integral f dif mu = sum_(x in X) f(x) w(x). $
]

#solution[
  For every $Sc$-partition $P$ of $X$ into $A_1, ..., A_m$, we have
  $
    cal(L)(f, P) = sum_(i = 1)^m mu(A_i) inf_(x in A_i) f(x) <= sum_(i = 1)^m
    sum_(x in A_i) w(x) f(x) = sum_(x in X) f(x) w(x).
  $
  Equality is a bit tricky. The idea is that since
  $
    sum_(x in X) f(x) w(x) = sup_(A subset.eq X, |A| < infinity) sum_(x in A)
    f(x) w(x),
  $
  $sum_(x in A) f(x) w(x)$ can be arbitrarily close to the infinite sum. Evey
  such $A$ can be trivially converted to the partition $P$ with ${x_1}, {x_2},
  ..., {x_m}$ where $A = {x_1, ..., x_m}$, so equality "kind of" holds.
]

#problem[
  Suppose $lambda$ denotes Lebesgue measure on $RR$. Give an example of sequence
  $f_1, f_2, ...$ of simple Borel measurable functions from $RR$ to $[0,
  infinity)$ such that $lim_(k -> infinity) f_k (x) = 0$ for every $x in RR$ but
  $lim_(k -> infinity) integral f_k dif lambda = 1$.
]

#solution[
  Consider an infinite sequence of disjoint sets $A_1, ... subset.eq RR$ with
  non-zero measure (such sequences can be trivially constructed). Then, define
  $ f_n (x) = 1 / mu(A_n) chi_A_n (x), $
  then
  $ integral f_n dif mu = 1 $
  for all $n$, but if $x in RR$, either $x$ is not in any $A_n$ (so $f_n (x) =
  0$ for all $n$), or $x$ is in some $A_i$ (so $f_n (x) = 0$ for all $n > i$).
  Either way, $lim_(n -> infinity) f_n (x) = 0$ for all $x in RR$.
]

#problem[
  Suppose $mu$ is a measure on a measurable space $(X, Sc)$ and $f: X -> [0,
  infinity]$ is a measurable function. Define $nu: Sc -> [0, infinity]$ by
  $ nu(A) = integral chi_A f dif mu $.
  for $A in Sc$. Prove that $nu$ is a measure on $(X, Sc)$.
]

#solution[
  Trivial.
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space and $f_1, f_2, ...$ is a sequence of
  nonnegative $Sc$-measurable functions. Define $f: X -> [0, infinity]$ by
  $f(x) = sum_(k = 1)^infinity f_k (x)$. Prove that
  $integral f dif mu = sum_(k = 1)^infinity integral f_k dif mu $.
]

#solution[
  Direct application of the Monotone Convergence Theorem.
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space and $f_1, f_2, ...$ are
  $Sc$-measurable functions from $X$ to $RR$ such that $sum_(k = 1)^infinity
  integral |f_k| dif mu < infinity$. Prove that there exists $E in Sc$ such that
  $mu(X without E) = 0$ and $lim_(k -> infinity) f_k (x) = 0$ for every $x in
  E$.
]

#solution[
  Without loss of generality, assuming $f_k >= 0$ for every $k$. Then, if
  $ f = sum_(k = 1)^infinity f_k, $
  we have
  $
    integral f dif mu = integral (sum_(k = 1)^infinity f_k) dif mu = sum_(k =
    1)^infinity integral f_k dif mu < infinity,
  $
  by the Monotone Convergence Theorem (previous exercise).

  Denote $E = {x in X: f(x) < infinity}$, then $mu(X without E) = 0$ and for all
  $x in E$,
  $ sum_(k = 1)^infinity f_k (x) = 0, $
  which implies $lim_(k -> infinity) f_k (x) = 0$ (the $n$-th term test).
]

#problem[
  Show that there exists a Borel measurable function $f: RR -> (0, infinity)$
  such that $integral chi_I f dif lambda = infinity$ for every nonempty open
  interval $I subset.eq RR$, where $lambda$ denotes Lebesgue measure on $RR$.
]

#solution[
  Consider the function
  $ g(x) = sum_(q_n in QQ) 1 / (4^n abs(x-q)), $
  where $q_1, q_2, ...$ is some enumeration of the rationals.
  This function can take the value $infinity$, so denote $X$ as the set of all
  $x in RR$ with $f(x) = infinity$. By @prob-borel-fn, we have $|{x
  in RR: f(x) >= 1}| <= 2$. However, this result can be generalize by taking
  $ A(beta) = union.big_(q_n in QQ) [q - beta^n, q + beta^n], $
  for some $beta in (0, 1)$. Then for every $x in.not A(beta)$,
  $ g(x) <= sum_(n = 1)^infinity 1 / ((4 beta)^n) = 1 / (4beta - 1) < infinity. $

  Measuring the set $RR without A(beta)$ yields $lambda(RR without
  A(alpha, beta)) <= 2 sum_(n = 1)^infinity beta^n = beta / (beta - 1)$.
  Clearly, $X$ must be a subset of all $A(beta)$, so its measure must be smaller
  than $beta / (beta - 1)$ for all $beta > 0$. Hence, $|X| = 0$.

  Now, if we let $f = g chi_(RR without X)$, then $f = g$ at most points.
  Hence, the integral of $f$ on some interval $I$ takes the same value as that
  of $g$, which is
  $
    integral chi_I f dif lambda = integral chi_I g dif lambda = sum_(q_n
    in QQ) integral (chi_I (x)) / (4^n abs(x - q_n)) dif lambda.
  $

  If $q_n in I_n$, the integral $integral (chi_I (x)) / (4^n abs(x - q_n))
  dif lambda$ diverges.
]

#problem[
  Give an example to show that the Monotone Convergence Theorem can fail if the
  hypothesis that $f_1, f_2, ...$ are nonnegative functions is dropped.
] <prob-cex-mct>

#solution[
  Let $E_1, E_2, ...$ be disjoint subsets of $RR$ such that $mu(E_1) >= mu(E_2)
  >= ...$. Then, define
  $ g_n = sum_(k = n)^infinity 1 / mu(E_k) chi_{E_k} $
  We have $integral g_n dif mu = infinity$ for all $n$ (proved with the real
  Monotone Convergence Theorem).

  Now, note that $g_n$ is decreasing to $0$, so if we define $f_n = -g_n$, then
  we have $ lim_(n -> infinity) integral f_n dif mu = -infinity != 0 = integral
  0 dif mu. $
]

#problem[
  Give an example to show that the Monotone Convergence Theorem can fail if the
  hypothesis of an increasing sequence of functions is replaced by a hypothesis
  of a decreasing sequence of functions.
]

#solution[
  $g_n$ in the previous problem.
]

#problem[
  Suppose $lambda$ is Lebesgue measure on $RR$ and $f: RR -> [-infinity,
  infinity]$ is a Borel measurable function such that $integral f dif lambda$
  is defined.
  + For $t in RR$, define $f_t RR -> [-infinity, infinity]$ by $f_t (x) = f(x -
    t)$. Prove that $integral f_t dif lambda = integral f dif lambda$ for all $t
    in RR$.
  + For $t in RR$, define $f_t RR -> [-infinity, infinity]$ by $f_t (x) = f(t x)
    $. Prove that $integral f_t dif lambda = 1/abs(t) integral f dif lambda$ for
    all $t in RR$.
]

#solution[
  This trivially follows from the translation invariant and the dilation invariant
  property of Lebesgue measure. Every partition corresponding to a lower
  Lebesgue sum of $f$ can be (reversibly) mapped to another partition corresponding
  to the same (or downscaled by $|t|$ in the dilation case) lower Lebesgue sum
  of $f_t$.
]

#problem[
  Suppose $Sc$ and $Tc$ are $sigma$-algebras on a set $X$ and $Sc subset.eq Tc$.
  Suppose $mu_1$ is a measure on $(X, Sc)$, $mu_2$ is a measure on $(X, Tc)$,
  and $mu_1 (E) = mu_2 (E)$ for all $E in Sc$. Prove that $f: X -> [0,
  infinity]$ is $Sc$-measurable, then $integral f dif mu_1 = integral f dif
  mu_2$.
]

#solution[
  Consider any $Tc$-partition $P$ of $X$ into $A_1, ..., A_m$. Let $c_k = inf_(x in
  A_k) f(x)$, then without loss of generality, assuming $c_1 < c_2 < ... < c_m
  <= c_(m + 1) = infinity$.

  Then,
  $
    cal(L)(f, P) &= sum_(i = 1)^m c_i mu(A_i)\
    &= sum_(i = 1)^m sum_(j = i)^m c_i mu(A_i sect f^(-1)([c_j, c_(j + 1))))\
    &<= sum_(i = 1)^m sum_(j = i)^m c_j mu(A_i sect f^(-1)([c_j, c_(j + 1))))\
    &= sum_(j = 1)^m c_j sum_(i = 1)^j mu(A_i sect f^(-1)([c_j, c_(j + 1))))\
    &= sum_(j = 1)^m c_j mu(f^(-1)[c_j, c_(j + 1)))\
    &= cal(L)(f, P'),
  $

  where $P'$ is the $Sc$-partition of $X$ into $f^(-1)[c_i, c_(i + 1)]$ for $i =
  1, ..., m$.

  Clearly, any $Tc$-partition has a lower Lebesgue sum at most that of another
  $Sc$-partition. Since any $Sc$-partition is also an $Tc$-partition, equality
  must hold:
  $ integral f dif mu_1 = integral f dif mu_2. $
]

#problem[
  Suppose that $(X, Sc, mu)$ is a measure space and $f_1, f_2, ...$ is a
  sequence of non-negative $Sc$-measurable functions on $X$. Define a function
  $f: X -> [0, infinity]$ by $f(x) = liminf_(k -> infinity) f_k (x)$.
  + Show that $f$ is an $Sc$-measurable function.
  + Prove that $ integral f dif mu <= liminf_(k -> infinity) integral f_k dif
    mu. $ <eq-fatou>
  + Give an example showing that the inequality in @eq-fatou can be a strict
    inequality even when $mu(X) < infinity$ and the family of functions
    ${f_k}_(k in ZZ^+)$ is uniformly bounded.
]

#solution[
  + $f(x) = lim_(k -> infinity) inf_(m >= k) f_m (x)$ clearly is
    $Sc$-measurable.
  + Define $h_k (x) = inf_(m >= k) f_m (x)$, then $h_k$ is increasing, so by the
    monotone convergence theorem,
    $
      integral f dif mu = integral lim_(k -> infinity) h_k dif mu = lim_(k ->
      infinity) integral h_k dif mu.
    $
    Now it suffices to prove $integral h_k dif mu <= inf_(m >= k) integral f_m
    dif mu$ holds for all $k$, i.e.
    $ inf_(m >= k) integral_(m >= k) (f_m - h_k) dif mu >= 0. $
    This clearly holds true since $h_k (x) = inf_(m >= k) f_m (x)$.
  + $f_n (x) = n chi_[0, 1/n] (x) exp(-n x)$, then $f = 0$ but $integral f_n
    dif lambda = 1$ for all $n$.
]

#problem[
  Give an example of a sequence $x_1, x_2, ...$ of real numbers such that
  $ lim_(n -> infinity) sum_(k = 1)^n x_k "exists in" RR $
  but $integral x dif mu$ is not defined, where $mu$ is the counting measure on
  $ZZ^+$ and $x$ is the function from $ZZ^+$ to $RR$ defined by $x(k) = x_k$.
]

#solution[
  By Riemann's arrangement theorem, any unconditionally convergent series
  satisfies this property.
]

#problem[
  Show that if $(X, Sc, mu)$ is a measure space and $f: X -> [0, infinity]$ is
  $Sc$-measurable, then
  $ mu (X) inf_X f <= integral f dif mu <= mu (X) sup_X f. $
]

#solution[
  This trivially holds as $f - inf_X f >= 0$ and $sup_X f - f >= 0$.
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space and $f_1, f_2, ...$ is a monotone
  (meaning either increasing or decreasing) sequence of $Sc$-measurable
  functions. Define $f: X -> [-infinity, infinity]$ by
  $ f(x) = lim_(k -> infinity) f_k (x). $
  Prove that if $integral |f_1| dif mu < infinity$, then
  $ lim_(k -> infinity) integral f_k dif mu = integral f dif mu. $
]

#solution[
  Define $f_k^+ (x) = max(f_k (x), 0)$, $f_k^- (x) = max(-f_k (x), 0)$. Then
  $f_k = f_k^+ - f_k^-$. Clearly $f_k^+$ and $f_k^-$ are monotone, so there
  exists

  $
    f^+ (x) = lim_(k -> infinity) f_k (x),\
    f^- (x) = lim_(k -> infinity) f_k (x).
  $

  We are sure that there exists no $x$ such that $f^+ (x) = f^- (x) = infinity$,
  so $f^+ - f^-$ are well defined. Trivially, this function is precisely $f$.

  We have:
  $
    infinity > integral |f_1| dif mu = integral (chi_X + chi_(RR without
      X))|f_1^+| dif mu > integral (f^+_1 + f^-_1) dif mu.
  $

  Effectively, after this, we reduces the problem to the case where $f_k$ is
  non-negative and monotonic. If $f_k$ is increasing then this is the Monotone
  Convergence Theorem, and when $f_k$ is decreasing, we can define $g_k = f_1 -
  f_k$, then $g_k$ is non-negative and increasing, hence:

  $
    integral (f_1 - f) dif mu = lim_(k -> infinity) integral (f_1 - f_k) dif mu
    = integral f_1 dif mu - lim_(k -> infinity) integral f_k dif mu.
  $

  Here, subtraction is well-defined since $integral f_1 dif mu < infinity$.
]

#problem[
  Henri Lebesgue wrote the following about his method of integration:

  #quote[
    I have to pay a certain sum, which I have collected in my pocket. I take the
    bills and coins out of my pocket and give them to the creditor in the order
    I find them until I have reached the total sum. This is the Riemann
    integral. But I can proceed differently. After I have taken all the money
    out of my pocket I order the bills and coins according to identical values
    and then I pay the several heaps one after the other to the creditor. This
    is my integral.
  ]

  Use 3.15 (MIRA) to explain what Lebesgue meant and to explain why integration
  of a function with respect to a measure can be thought of as partitioning the
  range of the function, in contrast to Riemann integration, which depends upon
  partitioning the domain of the function.
]

#solution[
  Trivial.
]

== Limits of Integrals & Integrals of Limits

#problem[
  Give an example of a sequence $f_1, f_2, ...$ of functions from $ZZ^+$ to $[0,
  infinity)$ such that
  $ lim_(k -> infinity) f_k (m) = 0 $
  for every $m in ZZ^+$ but $lim_(k -> infinity) integral f_k dif mu = 1$, where
  $mu$ is counting measure on $ZZ^+$.
]

#solution[
  $f_k (m) = cases(1 "if" m = k, 0 "otherwise").$
]

#problem[
  Give an example of a sequence $f_1, f_2, ...$ of continuous functions from
  $RR$ to $[0, infinity)$ such that
  $ lim_(k -> infinity) f_k (x) = 0 $
  for every $x in RR$ but $lim_(k -> infinity) integral f_k dif lambda =
  infinity$, where $lambda$ is Lebesgue measure on $RR$.
]

#solution[
  Let $Phi(x) = chi_[-1,1] (x) (1-|x|)$ with support $(-1, 1)$.
  Then, consider $f_k (x) = 3^k Phi(2^k (x - (1 - 3/2^k)))$.
]

#problem[
  Suppose $lambda$ is Lebesgue measure on $RR$ and $f: RR -> RR$ is a Borel
  measurable function such that $integral |f| dif lambda < infinity$. Define $g: RR
  -> RR$ by
  $ g(x) = integral_((-infinity, x)) f dif lambda. $
  Prove that $g$ is uniformly continuous on $RR$.
]

#solution[
  We want:
  $
    0 = lim_(delta -> 0) sup_(|x-y| < delta) |g(x) - g(y)| = lim_(delta -> 0)
    sup_(|x-y| < delta) abs(integral_((x, y)) f dif lambda).
  $
  This trivially follows from Theorem 3.28 of MIRA.
]

#problem[
  + Suppose $(X, Sc, mu)$ is a measure space with $mu(X) < infinity$. Suppose
    that $f: X -> [0, infinity)$ is a bounded $Sc$-measurable function. Prove
    that:
    $
      integral f dif mu = inf {sum_(j = 1)^m mu(A_j) sup_A_j f : A_1, ..., A_m
        "is an" Sc"-partition of" X}.
    $
  + Show that the conclusion of part 1 can fail if th hypothesis that $f$ is
    bounded is replaced by the hypothesis that $integral f dif mu  < infinity$.
  + Show that the conclusion of part 1 can fail if the hypothesis that $mu(X) <
    infinity$ is deleted.
]

#solution[
  + Let $M = sup_X f$, then
    $
      integral (M - f) dif mu\
      = sup {sum_(j = 1)^m mu(A_j) inf_A_j (M - f) : A_1,
        ..., A_m "is an" Sc"-partition of" X} \
      = M mu(X) - inf {sum_(j = 1)^m mu(A_j) sup_A_j (M - f) : A_1, ..., A_m
        "is an" Sc"-partition of" X}.
    $
    But it is also precisely equal to $M mu(X) - integral f dif mu$, hence QED.

  + Take $f(x) = 1/sqrt(x)$
    with $X = (0, 1)$. If $A_1, ..., A_m$ forms a $Sc$-partition
    of $(0, 1)$. and in order to make
    $ sum_(j = 1)^m mu(A_j) sup_A_j f < infinity$, we need $sup_A_j f <
    infinity$ for every $j$ such that $mu(A_j) > 0$. Denote $J = {j : mu(A_j) >
    0}$, then let $M = max_(j in J) sup_A_j f < infinity$. Now, it turns out that
    every $x in (0, 1/M^2)$ can not be in any $A_j$ such that $j in J$. Hence,
    $0 = mu(union_(j in.not J) A_j) >= mu((0, 1/M^2)) > 0$, a contradiction.
  + Take $f(x) = 1/x^2$ with $X = (1, infinity)$. If $A_1, ..., A_m$ forms a
    $Sc$-partition of $(1, infinity)$. and in order to make $ sum_(j = 1)^m mu(A_j)
    sup_A_j f < infinity$, we need $sup_A_j f = 0$ or $f(A_j) = {0}$ for every $j$ such
    that $mu(A_j) = infinity$. However, clearly $f(x) > 0$ for all $x$, so this
    is impossible! Hence, all $A_j$ must have finite measure, so their union,
    so does $(1, infinity)$, a contradiction.
]

#problem[
  Let $lambda$ denote Lebesgue measure on $RR$. Suppose $f: RR -> RR$ is a Borel
  measurable function such that $integral |f| dif lambda < infinity$. Prove
  that:
  $ lim_(k -> infinity) integral_([-k, k]) f dif lambda = integral f dif lambda. $
]

#solution[
  Let $h <= f$ be a simple function approximation to $f$ such that $integral h
  dif mu >= integral f dif mu - epsilon$. Then,
  $
    lim_(k -> infinity) integral_([-k,k]) f dif lambda >= lim_(k -> infinity)
    integral_([-k,k]) h dif lambda = integral_([-k,k]) h dif lambda >=
    integral_([-k,k]) f dif lambda - epsilon.
  $
  This holds for all $epsilon > 0$, so:
  $ lim_(k -> infinity) integral_([-k,k]) f dif lambda >= integral f dif lambda. $
]

#problem[
  Let $lambda$ denote Lebesgue measure on $RR$. Give an example of a continuous
  function $f: [0, infinity) -> RR$ such that $lim_(t -> infinity) integral_([0,
  t]) f dif lambda$ exists (in $RR$) but $integral_([0, infinity)) f dif lambda$
  is not defined.
] <prob-improper>

#solution[
  Consider $f(x) = sin(x)/x$ (at $x=0$ we let $f(x)=1$). Then,
  $
    integral_0^t (sin x) / x dif x &= "const" - integral_1^t (dif (cos x)) / x\
    &= "const" - ((cos x) / x)|_1^t - integral_1^t (cos x) / x^2 dif x.
  $
  As $t -> infinity$, we can see that the final expression is bounded (the
  integral is dominated by $integral_1^infinity 1/x^2 dif x = 1$).

  But,
  $
    integral_0^(2pi N) abs((sin x) / x) dif x &= sum_(n = 0)^(N - 1) integral_(2 pi n)^(2 pi
    (n + 1)) abs((sin x)/x) dif x\
    &>=sum_(n = 0)^(N - 1) 1 / (2pi (n + 1)) integral_(2 pi n)^(2 pi (n + 1)) |sin
    x|dif x\
    &= sum_(n = 0)^(N - 1) 2 / (pi (n + 1)) -> infinity "as" N -> infinity.
  $

  Basically, the integral conditionally converges. Trivially this is a
  valid counterexample to this problem.
]

#problem[
  Let $lambda$ denote Lebesgue measure on $RR$. Give an example of a continuous
  function $f: (0, 1) -> RR$ such that $lim_(n -> infinity) integral_((1/n,
  1)) f dif lambda$ exists (in $RR$) but $integral_((0, 1)) f dif lambda$ is not
  defined.
]

#solution[
  $f(x) = 1/x sin(1/x).$ By a change of variable ($u = 1/x$), this is precisely
  the integral in @prob-improper.
]

#problem[
  Verify the assertion in 3.38 (MIRA).
]

#solution[
  Trivial (it's not).
]

#problem[
  Verify the assertion in Example 3.41 (MIRA).
]

#solution[
  Trivial (it's also not).
]

#problem[
  + Suppose $(X, Sc, mu)$ is a measure space such that $mu(X) < infinity$.
    Suppose $p, r$ are positive numbers with $p < r$. Prove that if $f: X -> [0,
  infinity)$ is an $Sc$-measurable function such that $integral f^r dif mu <
  infinity$, then $integral f^p dif mu < infinity$.
  + Give an example to show that the result in part 1 can be false without the
    hypothesis that $mu(X) < infinity$.
]

#solution[
  + By the generalized AM-GM inequality, for every $alpha >= 0$,
    $ x^r + alpha dot 1 >= (alpha + 1) x^(r / (alpha + 1)), "for all" x >= 0. $
    Letting $alpha$ = $r/p - 1 > 0$, we have:
    $ x^r + (r / p - 1) >= r / p x^p. $

    Hence,
    $ infinity > integral f^r dif mu + (r / p-1)mu(X) >= r / p integral f^p dif mu. $
  + $integral_1^infinity 1/x = infinity$ and $integral_1^infinity 1/x^2 = 1$.
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space and $f in cal(L)^1 (mu)$. Prove that
  $ {x in X: f(x) != 0} $
  is the countable union of sets with finite $mu$-measure.
]

#solution[
  $ {x in X: f(x) != 0} = union.big_(n = 1)^infinity { x in X: |f(x)| > 1 / n}. $

  Clearly $mu({ x in X: |f(x)| > 1/n}) < n integral |f| dif mu < infinity$ for all $n$.
]

#problem[
  Suppose $ f_k (x) = ((1-x)^k cos k/x)/sqrt(x). $
  Prove that $lim_(k -> infinity) integral_0^1 f_k = 0$.
]

#solution[
  $|f_k (x)| <= 1/sqrt(x),$ so this trivially follows from the DCT.
]

#problem[
  Give an example of a sequence of nonnegative Borel measurable functions $f_1,
  f_2, ...$ on $[0, 1]$ such that both the following conditions hold:
  - $lim_(k -> infinity) integral_0^1 f_k = 0$;
  - $sup_(k >= m) f_k (x) = infinity$ for every $m in ZZ^+$ and every $x in [0,
    1]$.
]

#solution[
  Consider the following enumeration of $QQ sect (0, 1)$:
  $ 1 / 2, 1 / 3, 2 / 3, 1 / 4, 2 / 4, 3 / 4, 1 / 5, 2 / 5, 3 / 5, 4 / 5, ... $
  Continuing the pattern, we have the sequence $q_k = n_k/d_k$, where $n_k$ and
  $d_k$ are:

  $
    n_k&: 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, ...\
    d_k&: 2, 3, 3, 4, 4, 4, 5, 5, 5, 5, ....
  $

  Then, $d_k = O(sqrt(k))$. Define $f_k$ as:
  $ f_k = c_k chi_([q_k - 1 / d_k, q_k + 1 / d_k]) (x). $

  Now,
  $ integral_0^1 f_k = (2c_k) / d_k, $
  and for every $x$, we clearly see that if $c_k -> infinity$, then $sup_(k >=
  m) f_k (x) = infinity$, since $[q_k - 1/d_k, q_k + 1/d_k]$ covers the range
  $[0, 1]$ infinitely many times as $k -> infinity$.

  Hence, we just need to find some $c_k$ such that:
  - $c_k/sqrt(k) -> 0$ as $k -> infinity$ and
  - $c_k -> infinity$ as $k -> infinity$,
  which is very easy: $c_k = k^epsilon$ for any $epsilon in (0, 1/2)$.
]

#problem[
  Let $lambda$ denote Lebesgue measure on $RR$.
  + Let $f(x) = 1/sqrt(x)$. Prove that $integral_([0, 1]) f dif lambda = 2$.
  + Let $f(x) = 1/(1+x^2)$. Prove that $integral_(RR) f dif lambda = pi$.
  + Let $f(x) = (sin x)/x$. Show that the integral $integral_((0, infinity)) f
    dif lambda$ si not defined but $lim_(t -> infinity) integral_([0, t]) f dif
    lambda$ exists in $RR$.
]

#solution[
  + Trivial Calc 1 stuff. (if they want us to reinvent the wheel here then no).
  + Trivial Calc 1 stuff.
  + Already shown in @prob-improper.
]

#problem[
  Prove or give a counterexample: If $G$ is an open subset of $(0, 1)$, then
  $chi_G$ is Riemann integrable on $[0, 1]$.
]

#solution[
  Since $G$ is an open subset of $(0, 1)$, it must be the disjoint union of
  finitely many open intervals. Hence, trivially, $chi_G$ is Riemann integrable
  on $[0, 1]$.
]

#problem[
  Suppose $f in cal(L)^1 (RR)$.
  + For $t in RR$, define $f_t: RR -> RR$ by $f_t (x) = f(x - t)$. Prove that
    $ lim_(t -> 0) norm(f-f_t)_1 = 0. $
  + For $t in RR$, define $f_t: RR -> RR$ by $f_t (x) = f(t x)$. Prove that
    $ lim_(t -> 1) norm(f-f_t)_1 = 0. $
]

#solution[
  + Approximate $f$ by a step function $g = sum_(k=1)^n a_k chi_I_k <= f$ such
    that $norm(f-g)_1 < epsilon$. Define $g_t$ as the translation of $g$ by $t$
    unit (similarly to how $f_t$ is defined), then $norm(g - g_t)_1 -> 0$ as $t ->
    0$ due to the geometry of intervals. And since $norm(f-g)_1 =
    norm(f_t-g_t)_1 < epsilon$, we have $norm(f-f_t)_1 <= 2epsilon$. This holds
    for all $epsilon > 0$, hence QED.
  + We can use the same argument as above, with some differences:
    - $norm(f_t - g_t)_1 = t norm(f - g)_1 < t epsilon$.
    - Proving $norm(g - g_t)_1 -> 0$ is now a little bit more complicated, but a
      compact expression for the upper bound of this norm is $O(1) (t - 1) times
      mu("supp" g)$, where $"supp" g = {x in RR: g(x) != 0}$ is the support of
      $g$. Clearly that the support of a step function must have finite measure,
      so the upper bound fortunately converges to zero as $t -> 1$.
]

= Differentiation

== Hardy-Littlewood Maximal Function

#problem[
  Suppose $(X, Sc, mu)$ is a measure space and $h: X -> RR$ is an
  $Sc$-measurable function. Prove that
  $ mu({x in X: |h(x)| >= c}) <= 1 / c^p integral |h|^p dif mu $
  for all positive numbers $c$ and $p$.
]

#solution[
  $
    1 / c^p integral |f|^p dif mu &>= 1 / c^p integral_({x in X: |h(x)| >= c}) |h|^p
    dif mu\
    &>= 1 / c^p integral_({x in X: |h(x)| >= c}) c^p dif mu\
    &= mu({x in X: |h(x)| >= c}).
  $
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space with $mu(X) = 1$ and $h in
  cal(L)^1(mu)$. Prove that
  $
    mu({x in X: abs(h(x) - integral h dif mu) >= c}) <= 1 / c^2 (integral h^2 dif
      mu - (integral h dif mu)^2).
  $
]

#solution[
  Let $c = integral h dif mu$, then if f $f = h - c$,
  $
    integral |f|^2 dif mu = integral (h - c)^2 dif mu = integral h^2 dif mu - 2
    c integral h dif mu + c^2 = integral h^2 dif mu - c^2.
  $
  Then, the inequality trivially follows from the previous problem.
]

#problem[
  Suppose $(X, Sc, mu)$ is a measure space. Suppose $h in cal(L)^1 (mu)$ and
  $norm(h)_1 > 0$. Prove that there is at most one number $c in (0, infinity)$
  such that
  $ mu({x in X: |h(x)| >= c}) = 1 / c norm(h)_1. $
]

#solution[
  We easily see that if inequality holds, then $c = sup_X |h|$, so trivially QED.
]

#problem[
  Show that the constant 3 in the Vitali Covering Lemma cannot be replaced by a
  smaller positive constant.
]

#solution[
  Trivial (i'm lazy).
]

#problem[
  Prove the assertion left as an exercise in the last sentence of the proof of
  the Vitali Covering Lemma.
]

#solution[
  Trivial.
]

#problem[
  Verify the formula in Example 4.7 (MIRA) for the Hardy-Littlewood maximal
  function of $chi_([0,1])$.
]

#solution[
  Clearly $chi^*_1([0,1]) <= 1$ for all $x in RR$, with equality at $x in (0,
  1)$. For $x <= 0$, we have:
  $ 1 / (2t) integral_(x-t)^(x+t) chi^*_([0,1]) = 1 / (2t) max{0, min{1, x+t}}, $
  for all $t > -x$.

  This quantity is equal to:
  $
    1 / (2t) min{1, x+t} = cases(0 "if" t < -x, 1/2 + x/(2t) "if" -x<=t <= 1-x,
  1/(2t) "otherwise").
  $

  Ignoring the trivial $0$ branch, we see that the $1/(2t)$ branch is decreasing
  and $1/2+x/(2t)$ is increasing, so it must peak at exactly $x = 1 - t$. Hence,
  $ chi^*_([0, 1]) (x) = 1 / (2(1-x)). $
  Similarly, for all $x >= 1$, by symmetry, we have:
  $ chi^*_([0, 1]) (x) = 1 / (2x). $
]

#problem[
  Find a formula for the Hardy-Littlewood maximal function of $chi_([0,1] union
  [2, 3])$.
]

#solution[
  Proceed similarly.
]

#problem[
  Find a formula for the Hardy-Littlewood maximal function of $h: RR -> [0,
  infinity)$ defined by
  $ h(x) = cases(x "if" 0 <= x <= 1, 0 "otherwise"). $
]

#solution[
  Proceed similarly.
]

#problem[
  Suppose $h: RR -> RR$ is Lebesgue measurable. Prove that
  $ {b in RR: h^* (b) > c} $
  is an open subset of $RR$ for every $c in RR$.
]

#solution[
  Let $c$ be a real number and $g = |h| - c$.

  If $b in RR$ such that $h^* (b) > c$, there exists some $t > 0$ such
  that
  $ I = integral_(b-t)^(b+t) (|h|-c) = integral_(b-t)^(b+t) g > 0. $

  By Theorem 3.28 (MIRA), for every $epsilon > 0$, there exists some
  $delta(epsilon) > 0$
  such that for every Lebesgue measurable subset $A subset.eq (b-t, b+t)$ with
  Lebesgue measure at most $2delta(epsilon)$, $abs(integral_(A) g dif lambda) < epsilon$.

  From this, if we have $A, B subset.eq (b-t,b+t)$ such that their symmetric
  difference $A Delta B$ has Lebesgue measure at most $2delta(epsilon)$, then
  $ abs(integral_A g dif lambda - integral_B g dif lambda) <= abs(integral_(A
  without B) g dif lambda) + abs(integral_(B without A) g dif lambda) < 2epsilon$.

  If we let $A = (b-t, b+t)$ and $epsilon = I/2$, then
  $ I - integral_B g dif lambda < I, $
  which implies $integral_B g dif lambda > 0$.

  Now, consider a neighborhood $(b-r, b+r)$ of $b$. For each $b'$, we pick the
  radius $r' < t$ such that $(b'-r', b'+r') subset.eq A = (b-t, b+t)$, while making
  sure that $2abs(t-r') <= 2delta(I/2)$. In order to do so, it must be the case
  that:
  - $t-r' <= delta(I/2)$, and
  - $r+r' <= t$.
  It is clear that these two conditions can be trivially satisfied.

  Now, for each $b' in (b-r, b+r)$, we have:
  $ integral_(b'-r')^(b'+r') g dif lambda > 0, $
  hence $h^*(b') > 0$, QED.
]

#problem[
  Prove or give a counterexample: if $h: RR -> [0, infinity)$ is an increasing
  function, then $h^*$ is an increasing function.
]

#solution[
  Given $x_1, x_2$ in $RR$ such that $x_1 < x_2$, we have:
  $
    h^* (x_2) &= sup_(t > 0) integral_(x_2-t)^(x_2+t) h dif lambda\
    &>= sup_(t > 0)integral_(x_2-t)^(x_2+t) g dif lambda\
    &= sup_(t > 0)integral_(x_1-t)^(x_1+t) h dif lambda\
    &= h^* (x_1),
  $
  where $g(x) = h(x + x_1 - x_2)$. Clearly $g <= h$ as $h$ is increasing.
]

#problem[
  Give an example of a Borel measurable function $h: RR -> [0, infinity)$ such
  that $h^* (b) < infinity$ for all $b in RR$ but $sup {h^* (b): b in RR} =
  infinity$.
]

#solution[
  Let $h(x) = x$. Then, for every $b in RR$,
  $ integral_(b-t)^(b+t) h = 1 / 2 ((b+t)^2-(b-t)^2) = b t. $
  Hence, $h^* (b) = b/2$ for all $b in RR$.
]

#problem[
  Show that $abs({b in RR: h^* (b) = infinity}) = 0$ for every $h in cal(L)^1
  (RR)$.
]

#solution[
  A direct consequence of the Hardy-Littlewood maximal inequality:
  $
    abs({b in RR: h^* (b) = infinity}) <= abs({b in RR: h^* (b) > c}) <=
    3 / c norm(h)_1, forall c > 0.
  $
]

#problem[
  Show that there exists $h in cal(L)^1 (RR)$ such that $h^* (b) = infinity$ for
  every $b in QQ$
]

#solution[
  If there exists a function $delta$ such that:
  + $delta > 0$,
  + $integral_(-infinity)^infinity delta = I < infinity$,
  + $delta^* (0) = infinity$,

  then let $q_1, q_2, ...$ be an enumeration of the rationals, and define:
  $ f(x) = sum_(n = 1)^infinity 2^(-n) delta (x - q_n). $

  By the Monotone Convergence Theorem,
  $
    integral_(-infinity)^infinity f dif lambda = sum_(n = 1)^infinity 2^(-n)
    integral_(-infinity)^infinity delta = I < infinity,
  $
  so $f in cal(L)^1 (RR)$. But,
  $ f(x) >= 2^(-n) delta(x - q_n), $
  so
  $ f^* (q_n) >= 2^(-n) delta^* (q_n - q_n) = infinity => f^* (q_n) = infinity, $
  for all $n in ZZ^+$.

  Now all that's left is to define $delta$. One such example is:
  $ delta(x) = cases(1/sqrt(x) "if" 0 < abs(x) < 1, 0 "otherwise"). $

  We have:
  + $integral_(-infinity)^infinity delta = integral_(-1)^1 1/sqrt(x) dif x = 4$,
  + $delta^* (0) = sup_(0 < t < 1) 1/(2t) integral_(-t)^t 1/sqrt(x) dif x =
    sup_(0 < t < 1) 2/sqrt(t) = infinity$.
]

#problem[
  Suppose $h in cal(L)^1 (RR)$. Prove that
  $ abs({b in RR: h^* (b) >= c}) <= 3 / c norm(h)_1, $
  for every $c > 0$.
]

#solution[
  By Hardy-Littlewood maximal inequality:
  $
    abs({b in RR: h^* (b) >= c}) &= abs(sect.big_(n = 1)^infinity {b in RR: h^*
  (b) > c - 1/n}) \
    &< inf_(n in ZZ^+) 3 / abs(c-1/n) norm(h)_1 = 3 / c norm(h)_1.
  $
]

== Derivatives of Integrals

*For $f in cal(L)^1 (RR)$ and $I$ an interval of $RR$ with $0 < |I| < infinity$,
let $f_I$ denote the average of $f$ on $I$. In other words, $f_I = 1/abs(I) integral_I f$.*

#problem[
  Suppose $f in cal(L)^1 (RR)$. Prove that
  $ lim_(t -> 0^+) 1 / (2t) integral_(b-t)^(b+t) abs(f - f_([b-t,b+t])) = 0 $
  for almost every $b in RR$.
]

#solution[
  By the Lebesgue differentiation theorem and one of its corollaries,
  $ lim_(t -> 0^+) 1 / (2t) integral_(b-t)^(b+t) abs(f-f(b)) = 0 $
  and
  $ f(b) = lim_(t-> 0^+) f_([b-t, b+t]) $
  for almost every $b in RR$.

  Fix $b$ such that the two equalities hold.
  Then, for every $epsilon > 0$, there exists some $T$ such that:
  $ 1 / (2t) integral_(b-t)^(b+t) abs(f-f(b)) < epsilon / 2 $ and
  $ abs(f(b) - f_([b-t, b+t])) < epsilon / 2 $
  for every $0 < t < T$. Combining this yields
  $
    1 / (2t) integral_(b-t)^(b+t) abs(f-f_([b-t, b+t])) < 1 / (2t)
    integral_(b-t)^(b+t) (abs(f-f(b)) + abs(f(b) - f_([b-t, b+t]))) < epsilon
  $
  for all $0 < t < T$.

  Hence,
  $ lim_(t -> 0^+) 1 / (2t) integral_(b-t)^(b+t) abs(f-f_([b-t, b+t])) = 0. $.
]

#problem[
  Suppose $f in cal(L)^1 (RR)$. Prove that
  $ lim_(t -> 0^+) sup {1 / abs(I) integral_I abs(f-f_I): I "is an interval of length" t "containing" b} = 0 $
  for almost every $b in RR$.
]

#solution[
  Denote $J(b, t)$ as the set of all intervals with length $t$ containing $b$.
  Then,
  $
    sup_(I in J(b, t)) 1 / abs(I) integral_I abs(f-f_I) <= 1 / t sup_(I in J(b,
      t)) integral_I abs(f-f(b)) + sup_(I in J(b, t)) abs(f_I - f(b)).
  $

  The two terms both approach $0$ as $t->0^+$ for almost every $b in RR$:

  - $1/t sup_(I in J(b, t)) integral_I |f-f(b)| <= 1/t integral_(b-t)^(b+t)
    abs(f-f(b)) -> 0$ for almost every $b in RR$.
  - For every $I in J(b, t)$, we have $ abs(f_I - f(b)) = 1/t abs(integral_I
    (f-f(b))) <= 1/t integral_I abs(f-f(b)) <= 1/t integral_(b-t)^(b+t)
    abs(f-f(b)) -> 0$ for almost every $b in RR$.
]

#problem[
  Suppose $f: RR -> RR$ is a Lebesgue measurable function such that $f^2 in
  cal(L)^1 (RR)$. Prove that
  $ lim_(t->0+) 1 / (2t) integral_(b-t)^(b+t) |f-f(b)|^2 = 0 $ for almost
  every $b in RR$.
]

#solution[
  We have:
  $
    1 / (2t) integral_(b-t)^(b+t) abs(f-f(b))^2 &= 1 / (2t) integral_(b-t)^(b+t)
    (f^2 - 2 f(b) f + f(b)^2)\
    &= 1 / (2t) integral_(b-t)^(b+t) (f^2 - f^2(b)) + f(b) (f(b) - f_((b-t,
        b+t))).
  $
  Both of the two terms approach $0$ as $t -> 0^+$ for almost every $b in RR$.
]

#problem[
  Prove that the Lebesgue Differentiation Theorem still holds if the hypothesis
  that $integral_(-infinity)^infinity abs(f) < infinity$ is weakened to the
  requirement that $integral_(-infinity)^x abs(f) < infinity$ for all $x in RR$.
]

#solution[
  Define $tilde(f)$ as:
  $ tilde(f) (x) = cases(0 "if" x > x_0, f(x) "otherwise"), $
  then $integral tilde(f) dif lambda = integral_(-infinity)^(x_0) f < infinity$.
  Hence, for every $x_0 in RR$, $tilde(f) in cal(L)^1 (RR)$. Applying the LDT to
  $tilde(f)$ yields that $g'(x) = f(x)$ for almost every $x < x_0$.

  Letting $x_0$ takes the value of a countable sequence to $infinity$ (e.g.
  $x_0 = 1, 2, ..., n, ...$), we obtain that $g'(x) = f(x)$ must hold for almost
  every $x in RR$.
]

#problem[
  Suppose $f: RR -> RR$ is a Lebesgue measurable function. Prove that
  $ abs(f(b)) <= f^* (b) $
  for almost every $b in RR$.
]

#solution[
  Clearly $f^* (b) plus.minus f(b) = sup_(t > 0) 1/(2t) integral_(b-t)^(b+t)
  (abs(f) plus.minus f) >= 0$ for all $b in RR$.
]

#problem[
  Prove that if $h in cal(L)^1 (RR)$ and $integral_(-infinity)^s h = 0$ for all
  $s in RR$, then $h(s) = 0$ for every $s in RR$.
]

#solution[
  This trivially follows from Lebesgue Differentation Theorem, second version.
]

#problem[
  Give an example of a Borel subset of $RR$ whose density at $0$ is not defined.
]

#solution[
  Let $ E = union.big_(n = 0)^(infinity) [(1/3)^(2n+1), (1/3)^(2n)]. $

  Then,
  $
    abs(E sect (-(1/3)^(2k), (1/3)^(2k))) = sum_(n = k)^infinity
    abs([(1/3)^(2n+1), (1/3)^(2n)]) = sum_(n=k)^infinity 2 / 3 dot (1 / 9)^n = 1 / (12
    dot 9^k).
  $

  As $k -> infinity$, we have:
  $
    lim_(k -> infinity) abs(E sect (-(1/3)^(2k), (1/3)^(2k))) / ((1 / 3)^(2k)) =
    1 / 12.
  $

  However, if one redo the calculation with $t = (1/3)^(2k+1)$, we have:
  $
    lim_(k -> infinity) abs(E sect (-(1/3)^(2k), (1/3)^(2k))) / ((1 / 3)^(2k+1)) =
    1 / 27.
  $

  Hence, clearly the density limit does not exist.
]

#problem[
  Give an example of a Borel subset of $RR$ whose density at $0$ is $1/3$.
]

#solution[
  For any $s in (0, 1)$, let $I_n = (1/(n+1), 1/(n+1) + s/(n(n+1)))$ and take
  $E$ as the union of all such $I_n$'s.
  Then, we can calculate $ d(t) = |E sect (-t, t)|$. Similarly to the previous
  example, we will only concern ourselves with the values of $d(t)$ when $t =
  1/(n+1)$ and $t=1/(n+1) +s/(n(n+1))$. The other values of $t$ are squeezed
  between them, and it is provable (albeit somewhat tedious) that only the two
  cases mentioned matter here.

  - $m(1/(n+1)) = sum_(k = n + 1)^infinity s/(k(k+1)) = s/(n+1)$.
  - $m(1 / (n+1) + s / (n(n+1))) = sum_(k = n)^infinity s / (k(k+1)) = s / n$.

  Either way, the limit $(m(t))/t$ both approaches $s$ as $n -> infinity$, so by
  letting $s = 1/3$, we have our desired example.
]

#problem[
  Prove that if $t in [0, 1]$, then there exists a Borel set $E subset.eq RR$
  such that the density of $E$ at 0 is $t$.
]

#solution[
  See previous problem.
]

#problem[
  Suppose $E$ is a Lebesgue measurable subset of $RR$ such that the density of
  $E$ equals 1 at every element of $E$ and equals 0 at every element of $RR
  without E$. Prove that $E = diameter$ or $E = RR$.
]

// https://math.stackexchange.com/questions/4199779/no-proper-measurable-subset-of-real-number-has-density-only-0-and-1
#solution[
  Assuming $E$ is non-empty. For every $b in.not E$, we have:
  $
    0 = lim_(t->0^+) abs(E sect (x-t, x+t)) / (2t) = lim_(t->0^+) 1 / (2t)
    integral_(b-t)^(b+t) chi_E,
  $
  and from the inequality used in the proof of 4.19 (MIRA),
  the derivative of $G(x) = integral_a^x chi_(RR without E)$ at $b$ must be 0.
  Here $a$ is an arbitrary constant.

  Similarly, the derivative of $F(x) = integral_a^x chi_(E)$ at any $b in E$ must
  be 1, and since $F(x) + G(x) = x - a$ for all $x in RR$, we
  have $F'(x) = chi_E$ everywhere.

  For a given $b > a$, the Mean Value Theorem states that there exists some $c
in (a, b)$ such that:
  $ chi_E (c) = F'(c) = (F(b)-F(a)) / (b-a) = (|E sect (a, b)|) / (b-a). $

  From this, either $abs(E sect (a, b)) = b - a$ or $0$ for every $b > a$.
  If $abs(E sect (a, b)) = 1$, then the density of every point in $(a, b)$ must
  be 1, which means $(a, b) subset.eq E$. Similarly, if $abs(E sect (a, b)) =
  0$, then $(a, b) subset.eq RR without E$.

  This is a bizarre set of conditions, which could only hold in the most trivial
  cases: $E = diameter$ or $E = RR$. Assuming otherwise, then there must be some
  $u in E$ and $v in.not E$, and letting $a = u - epsilon$ and $b = v + epsilon$
  clearly yield a contradiction: $(a, b)$ can't be in $E$ (it contains $v$) or
  in $RR without E$ (it contains $u$).
]

= Product Measures

#let ox = math.times.circle

== Product of Measure Spaces

#problem[
  Suppose $(X, Sc)$ and $(Y, Tc)$ are measurable spaces. Prove that if $A$ is a
  nonempty subset of $X$ and $B$ is a nonempty subset of $Y$ such that $A times
  B in Sc ox Tc$, then $A in Sc$ and $B in Tc$.
]

#solution[
  Let $a in A$ and $b in B$. Then, the cross-sections $A$ = $[A times B]^b$ and
  $B = [A times B]_a$ are $Sc$-measurable and $Tc$-measurable, respectively.
]

#problem[
  Suppose $(X, Sc)$ is a measurable space. Prove that if $E in Sc ox Sc$, then
  $ {x in X: (x, x) in E} in Sc. $
]

#solution[
  Let $Tc$ be the set of all subsets $E subset.eq X times X$ such that ${x in
  X: (x, x) in E} in Sc$.

  Then, $Tc$ contains all $A times B$ where $A in Sc$ and $B in Sc$:
  $ {x in X: (x, x) in A times B} = A sect B in Sc. $

  Finally, to finish the proof, we need to prove that $Tc$ is a
  $sigma$-algebra, i.e. it is closed under complementation and countable union:
  - *Complementation*: If $E in Tc$ then ${x in X: (x, x) in (X times X)
    without E} = X without {x in X: (x, x) in E} in Sc$, so $X times X) without
    E in Tc$.
  - *Countable union*: If $E_k in Tc$ for $k = 1, 2, ...$ then $ {x in X: (x, x)
    in union.big_(k=1)^infinity E_k} = union.big_(k=1)^infinity {x in X: (x, x)
    in E_k} in Sc$, so $union.big_(k=1)^infinity E_k in Tc$.
]

#problem[
  Let $cal(B)$ denote the $sigma$-algebra of Borel subsets of $RR$. Show that
  there exists a set $E subset.eq RR times RR$ such that $[E]_a in cal(B)$ and
  $[E]^a in cal(B)$ for every $a in RR$, but $E in.not cal(B) times cal(B)$.
]

#solution[
  Let $V$ be some non-Borel measurable set. Then, define $E = {(x, x): x in V}$.
  The cross-sections of $E$ at any given point is either a singleton or the
  empty set, which are both clearly measurable.

  However, $E in.not cal(B) times cal(B)$. Assuming otherwise, since $f: x |->
  (x, x)$ is a Borel measurable function from $RR$ to $RR times RR$, its
  preimage of $E$ must also be measurable. However, the preimage itself is $V$,
  which is a non-Borel measurable set, a contradiction.
]

#problem[
  Suppose $(X, Sc)$ and $(Y, Tc)$ are measurable spaces. Prove that if $f: X ->
RR$ is $Sc$-measurable and $g: Y -> RR$ is $Tc$-measurable then $h: X times Y ->
RR$ defined by $h(x, y) = f(x)g(y)$, then $h$ is $(Sc ox Tc)$-measurable
]

#solution[
  Define $hat(f)(x, y) = f(x)$. Then, $hat(f)^(-1) (E) = f^(-1) (E) times Y$,
  which is $(Sc ox Tc)$-measurable as long as $f^(-1) (E)$ is $Sc$-measurable.
  Hence, $hat(f)$ is $(Sc ox Tc)$-measurable. Similarly, define $hat(g)(x, y) = g(y)$,
  which is also $(Sc ox Tc)$-measurable. Since $h$ is simply the product of
  $hat(f)$ and $hat(g)$, it follows that $h$ is $(Sc ox Tc)$-measurable as well.
]

#problem[
  Verify the assertion in Example 5.11 (MIRA) that the collection of finite
  unions of intervals of $RR$ is closed under complementation.
]

#solution[
  Assuming $E = union.big_(n = 1)^N I_n$, where $I_n$ are intervals.

  Then, $RR without E = sect.big_(n=1)^N (RR without I_n)$.
  Since every $RR without I_n$ can be written as the union of at most two
  interval $I_n^0$ and $I_n^1$, we have:
  $
    RR without E = sect.big_(n=1)^N (I_n^0 union I_n^1) = union.big_(b in {0, 1}^N)
    sect.big_(n=1)^N I_n^(b_n).
  $

  This is a finite union of intervals of $RR$, so clearly it belongs to the
  algebra.
]

#problem[
  Verify the assertion in Example 5.12 (MIRA) that the collection of countable
  unions of intervals of $RR$ is not closed under complementation.
]

#solution[
  The irrationals (complementation of $QQ$) can't be written as any countable
  union of intervals, due to $QQ$ being dense in $RR$.
]

#problem[
  Suppose $cal(A)$ is a nonempty collection of subsets of a set $W$. Show that
  $cal(A)$ is an algebra on $W$ if and only if $cal(A)$ is closed under finite
  intersections and under complementation.
]

#solution[
  This trivially holds: under the assumption of closeness under complementation,
  closed under finite intersections and closed under finite unions is the same
  thing. The only slightly non-trivial thing is proving $cal(A)$ contains the
  empty set if it's closed under finite intersection and complementation: take
  any $A in cal(A)$, then $A sect (W without A) = diameter in cal(A)$, QED.
]

#problem[
  Suppose $mu$ is a measure on a measurable space $(X, Sc)$. Prove that the
  following are equivalent:
  + The measure $mu$ is $sigma$-finite.
  + There exists an increasing sequence $X_1 subset.eq X_2 subset.eq ...$ of
    sets in $Sc$ such that $X = union.big_(k=1)^infinity X_k$ and $mu(X_k) <
  infinity$ for every $k in ZZ^+$.
  + There exists an disjoint sequence $X_1, X_2, X_3, ...$ of
    sets in $Sc$ such that $X = union.big_(k=1)^infinity X_k$ and $mu(X_k) <
  infinity$ for every $k in ZZ^+$.
]

#solution[
  2 and 3 are trivially equivalent. 2 (or 3) implies 1 by definition.

  1 implies 3 since if $X = union.big_(k=1)^infinity X_k$, where each $mu(X_k) <
    infinity$, then
  $ X'_k = X_k without union.big_(k' < k) X_(k'), mu(X'_k) <= mu(X_k) < infinity $
  is the disjoint sequence we need.
]

#problem[
  Suppose $mu$ and $nu$ are $sigma$-finite measures. Prove that $mu times nu$ is
  a $sigma$-finite measure.
]

#solution[
  Countable times countable is still countable:
  $
    X times Y = union.big_(k=1)^infinity X_k times union.big_(l=1)^infinity Y_l
    = union.big_((k, l) in ZZ_+^2) (X_k times Y_l),
  $
  where $(mu times nu)(X_k times Y_l) = mu(X_k) nu(Y_l) < infinity$.
]

#problem[
  Suppose $(X, Sc, mu)$ and $(Y, Tc, nu)$ are $sigma$-finite measure spaces.
  Prove that if $omega$ is a measure on $Sc ox Tc$ such that $omega(A times B) =
  mu(A) nu(B)$ for all $A in Sc$ and $B in Tc$, then $omega = mu times nu$.
]

#solution[
  Let $W$ be the set of all $E in Sc ox Tc$ such that $omega(E) = (mu times
nu)(E) = integral_X integral_Y chi_E (x, y) dif nu(y) dif mu (x).$

  Then, $W$ contains all finite unions of measurable rectangles, so we will show
  that it is a monotone class:

  If $E_1 subset.eq E_2 subset.eq ...$ such that $E_n in W$, then
  $
    omega(union.big_(n = 1)^infinity E_n) = lim_(n -> infinity) omega(E_n) =
    lim_(n -> infinity) (mu times nu)(E_n) = (mu times nu)(union.big_(n =
      1)^infinity E_n).
  $

  Similarly, if $E_1 supset.eq E_2 supset.eq ...$ such that $E_n in W$, then
  $
    omega(sect.big_(n = 1)^infinity E_n) = (mu times nu)(sect.big_(n =
      1)^infinity E_n).
  $

  Hence, $W$ is a monotone class that contains the algebra of measurable
  rectangles, so it must contain the smallest $sigma$-algebra generated by these
  rectangles, $Sc ox Tc$.
]
