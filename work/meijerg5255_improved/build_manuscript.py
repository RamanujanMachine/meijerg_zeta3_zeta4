"""Build the complete revised standalone manuscript, retaining prior proof."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
OUT=ROOT/'results/meijerg5255_improved'

source=(ROOT/'results/meijerg5255_arithmetic/meijerg_zeta3_zeta4_arithmetic.tex').read_text()
source=source.replace('0.0113626','0.01634832').replace('0.2190118','0.22626234')
source=source.replace('An arithmetic proof with exact rational certificates',
                      'Improved arithmetic bounds with a second-order trace certificate')
source=source.replace('double poles, an exact prime-carry partition, and a finite-field sum\nthat supplies additional common factors.',
                      'double poles, an exact prime-carry partition, and a root deformation\nwhose trace cancels through second order at selected primes.')
source=source.replace('These are first-order divisibility\nstatements.  No unproved second-order enhancement is included.',
                      'These are first-order divisibility statements. The next section\nproves a further factor on two smaller periodic intervals.')
trace=(WORK/'arithmetic/second_order_trace.tex').read_text()

conclusion=r'''
\section{The improved divisor and its density}
Let $\mathcal T=(1/10,2/19)\cup(11/12,15/16)$, and let
$G_n^{\rm old}$ be the divisor from the baseline carry profile and the
fourteen first-order shells. Define
\[
 J_n=\prod_{\substack{p>29,\ p^2>30n,\ p\nmid n\\
                  \{n/p\}\in\mathcal T}}p,
 \qquad G_n^{\rm new}=G_n^{\rm old}J_n.
\]
The second-order argument proves an additional factor at each of these
primes, simultaneously for both normalizations. Indeed, on these cells
the baseline exponent is $c+1$, the first-order exponent is $c+2$, and
(SG) gives $c+3$, where $c=2\lfloor15n/p\rfloor-3\lfloor10n/p\rfloor$.
Thus no existing prime factor has been counted twice. We have
\[
 \frac{6C_nd_{19n}^3}{G_n^{\rm new}}(Q_n,P_{3,n})\in\mathbb Z^2,
 \qquad
 \frac{6C_nd_{19n}^4}{G_n^{\rm new}}(Q_n,P_{3,n},P_{4,n})
     \in\mathbb Z^3.                                      \tag{I2}
\]
The two rows can use different lcm powers because their harmonic orders
differ. The primewise argument also chooses the cutoff
$\eta=p\lceil2n/p\rceil$ separately for each prime. These are equal
readouts of the same conserving family, so the different choices do not
change the approximant.

For an interval $0<a<b\le1$, put
\[
 \mathcal D(a,b)=\sum_{t=0}^{\infty}
             \left(\frac1{t+a}-\frac1{t+b}\right).
\]
The prime number theorem and the bounded profiles give the density
\[
 \gamma_{\rm new}=\gamma_{\rm old}
       +\mathcal D(1/10,2/19)+\mathcal D(11/12,15/16).
\]
Small excluded primes contribute $O(\sqrt n)$ to $\log G_n$; prime
divisors of $n$ contribute $O(\log n)$. For any fixed number of periods
the prime number theorem evaluates the finite sum. The remaining
periods involve only $p\le n/K$ and have density $O(1/K)$, which
justifies passage to the whole series.

The omitted tails can also be enclosed without numerical integration.
For $f(t)=(t+a)^{-1}-(t+b)^{-1}$, convexity gives
\[
 \log\frac{K+b}{K+a}+\frac{f(K)}2
 \le\sum_{t=K}^{\infty}f(t)
 \le\log\frac{K-\frac12+b}{K-\frac12+a}.
\]
At $K=1000$, enclosing each logarithm by its positive atanh series with
an exact rational remainder gives
\[
\begin{aligned}
 \gamma_{\rm old}&>29.9127079828158127,\\
 \mathcal D(1/10,2/19)&>0.5075180069435895,\\
 \mathcal D(11/12,15/16)&>0.0383212540460914.
\end{aligned}
\]
The complete rational lower certificate is
\[
 \gamma_{\rm new}\ge
 \frac{30458547243805493774844991}{10^{24}}
 >30.45854724380549>30.45854724.                         \tag{DEN}
\]

\section{Consequences for reduced denominators and delta}
For $B=0$ use the first integer form in (I2); for $B\ne0$ use the
second. The reduced denominator divides its integer denominator.
Since $\log C_n=30n\log(3/2)+o(n)$ and
$\log d_{19n}=19n+o(n)$, the accepted growth estimate and (DEN) imply
\[
\begin{array}{c|c|c}
\text{readout}&\limsup\log q_N/n\text{ is less than}
             &\liminf\delta_N\\\hline
B=0,\ A\ne0&91.992989325866&>0.22626234\\
B\ne0&110.992989325866&>0.01634832
\end{array}
\]
For example, combining the error exponent $E>112.807539247454$
with either displayed height bound $H$ gives $\liminf\delta_N\ge E/H-1$;
exact rational cross-multiplication verifies the stated decimals.
All factors depending only on the fixed coefficients $A,B$ have zero
exponential cost. This proves the result stated at the beginning.
It is a bound on this approximation sequence, not an upper bound on an
irrationality measure.

\section{Numerical comparison and verification}
The previous arithmetic bounds were $0.2190118$ for pure $\zeta(3)$
and $0.0113626$ for the joint readout. The new factors improve them to
$0.22626234$ and $0.01634832$, respectively, without changing the
trajectory or initial-condition matrix.

Here are actual reduced-denominator deltas, evaluated with Arb twice
at each depth using two precisions differing by 100 decimal digits:
\[
\begin{array}{r|rr}
N&\delta_N(1,0)&\delta_N(1,1)\\\hline
1000&0.226270805823&0.016685345951\\
2000&0.227250300699&0.016967611459\\
4000&0.226324705427&0.016428111403\\
8000&0.226391177278&0.016262704080
\end{array}
\]
Finite-depth oscillations can put a value below an asymptotic lower
bound. These data do not identify the exact limiting delta. Fits to the
last three depths give $0.22615555$ and $0.01603797$; the fitted error
exponents agree with the accepted value $112.80753924745\ldots$.

The two new windows pass 843 eligible prime instances at
$n=49,99,249,499,999,1999,3999,7999$. The complete forms (I2) and
reduced-denominator divisibility were checked additionally at
$n=1,2,3,10$, for each pair
$(1,0),(0,1),(1,1),(1,-1),(2,3),(-7,5)$.
Two independently written exact arrangement checks find the same nine
cells and prove their integer lifts symbolically. These finite numerical
tests supplement the uniform trace argument; they do not establish it.

The result does not certify an optimal gcd. At $n=7999$ the remaining
eligible joint surplus outside this profile consists only of the prime
$1321$, with logarithmic density $\log(1321)/7999\approx0.00089838$.
No further uniform factor is inferred from that isolated residue.
'''
begin=source.index('\\section{The divisor density and the reduced denominator}')
end=source.index('\\paragraph{Related arithmetic methods.}',begin)
source=source[:begin]+trace+conclusion+source[end:]
needle='The chamber and density checks themselves use only Python\'s standard'
insert=r'''
The improved package adds the following checks, also run from its root:
\begin{verbatim}
python work/meijerg5255_improved/arithmetic/second_order_certificate.py
python work/meijerg5255_improved/audit/independent_affine_chambers.py
python work/meijerg5255_improved/residuals/infinite_density.py
python work/meijerg5255_improved/residuals/final_bound_certificate.py
python work/meijerg5255_improved/verify_improved.py
python work/meijerg5255_improved/residuals/measure_delta.py
\end{verbatim}
The last command reuses the included exact native-column checkpoints.
To regenerate them, use \texttt{residuals/profile.py} with the desired
depths; its CMF reconstruction uses \texttt{ramanujantools}.

'''
source=source.replace(needle,insert+needle)
dest=OUT/'meijerg_zeta3_zeta4_improved.tex'
dest.write_text(source)
print(dest)
