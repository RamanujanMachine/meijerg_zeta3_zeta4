from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
OUT=ROOT/'results/meijerg5255_arithmetic'
config_path=OUT/'final_config.json'
config=json.loads(config_path.read_text())if config_path.exists()else dict(gamma='29.2366',delta3='0.2101873',delta4='0.0052809',extra_density='3',extra_tex='')
head=r'''\documentclass[11pt]{article}
\usepackage[margin=23mm]{geometry}
\usepackage[T1]{fontenc}
\usepackage{lmodern,amsmath,amssymb,amsthm,mathtools,booktabs,microtype,hyperref}
\hypersetup{colorlinks=true,linkcolor=blue,urlcolor=blue}
\newtheorem{theorem}{Theorem}
\newcommand{\Z}{\mathbb Z}
\allowdisplaybreaks
\setlength{\emergencystretch}{2em}
\title{CMF conservation and the arithmetic of\\$A\zeta(3)+B\zeta(4)$\\\large The trajectory $(16,17,-11,-12,-10;2,1,0,-1,-2)$}
\author{An arithmetic proof with exact rational certificates}
\date{10 October 2026}
\begin{document}\maketitle
\begin{abstract}
For the specified native MeijerG CMF, we establish a uniform common
divisor of the two prescribed zeta readouts. Taking their exponential
growth and approximation-error rates as given, the arithmetic estimate
implies $\liminf\delta_N>@@D4@@$ for every fixed integer pair
$(A,B)\ne(0,0)$, and $\liminf\delta_N>@@D3@@$ when $B=0$.
The proof uses an admissible reordered CMF path, a rational kernel with
double poles, an exact prime-carry partition, and a finite-field sum
that supplies additional common factors. These bounds do not assert
that the observed finite-depth deltas are the exact asymptotic values.
\end{abstract}

\section{The statement and the accepted analytic input}
Use $\operatorname{MeijerG}(5,2,5,5,1)$ with initial point
$(1,1,0,0,0;0,0,0,0,0)$ and the direction in the title. Put $n=N-1$,
exactly matching the user's indexing. The accepted initial-condition
matrix is
\[
 R_{A,B}=\begin{pmatrix}0&0&-6A&3A-2B\\12&0&0&0\end{pmatrix}.
\]
In all statements $A,B$ are fixed integers; they do not vary with $N$.
Let $r_N(A,B)$ be the quotient of the two entries of $R_{A,B}W_ne_0$.
Its reduced positive denominator is denoted $q_N(A,B)$.

The analytic input, used without reproving it, is
\[
 \log|Q_n|=\sigma n+o(n),\qquad
 \left|\zeta(s)-\frac{P_{s,n}}{Q_n}\right|
       \le \exp(-En+o(n)),\quad s=3,4,
\]
where the exact readouts $Q_n,P_{s,n}$ are identified below and
\[
 \sigma=53.287583322620205\ldots,\qquad
 E=112.807539247454680\ldots .
\]
Exact rational isolation and logarithm certificates for the associated
spectral constants accompany the proof. In particular
\[
 \sigma+30\log(3/2)<65.451536565866,\qquad E>112.807539247454.
\]
The full limiting matrix also has an eigenvalue $-1$; the selected
readouts' elimination of that mode is part of the given analytic input.
The triangle inequality gives the same error upper exponent $E$ for
every fixed $A\zeta(3)+B\zeta(4)$.

\begin{theorem}
Under this accepted analytic input, the reduced approximants satisfy
\[
 \boxed{\liminf_{N\to\infty}\delta_N(A,B)>@@D4@@}
 \quad\text{for every fixed }(A,B)\in\Z^2\setminus\{(0,0)\}.
\]
If $B=0$, the stronger estimate is
\[
 \boxed{\liminf_{N\to\infty}\delta_N(A,0)>@@D3@@}\qquad(A\ne0).
\]
Here $\delta_N=-1-\log|A\zeta(3)+B\zeta(4)-r_N|/\log q_N$ whenever
$q_N>1$ and the error is nonzero; an exact approximant may equivalently
be assigned $\delta_N=+\infty$. Fixed rational coefficients have the same
exponents after multiplication by one fixed denominator.
\end{theorem}

\section{What multiplication order contributes}
Conservation identifies products along admissible shifted lattice paths
with the same endpoints. It does not say that matrices evaluated at a
single vertex commute. We first decrease $a_2,a_3,a_4$, then increase
$a_0,a_1$, then increase $b_0,b_1$, and finally decrease $b_3,b_4$.
This order creates a long interval of triple zeros before the last
contour shift is needed. It also exposes factorial and harmonic blocks
that are invisible in an entrywise estimate of the original trajectory
matrix.

There is no requirement to use the same arithmetic certificate for the
two initial rows. Nor must one use the same path at different primes.
For a cut $w$, write $W_n=U_wV_w$. The identity
\[
 re_\text{end}=rW_ne_0=\sum_i(rU_w)_i(V_we_0)_i
\]
(with the leftmost expression understood simply as the endpoint scalar)
gives the valid certificate
\[
 v_p(rW_ne_0)\ge \min_i v_p\bigl((rU_w)_i(V_we_0)_i\bigr).
\]
One may maximize this independently for each $p$ and each initial row.
For the mixed numerator it is also useful to split
$r_{A,B}=Ar_3+Br_4$: bounds proved separately for $r_3$ and $r_4$ imply a
bound for every integer combination. This can be stronger than applying
one entrywise estimate to the already combined row.

The accompanying exact path experiments demonstrate this freedom in the
present CMF. They are not the justification for an asymptotic divisor.
The uniform argument below exposes one convenient rational readout and
then proves its primewise divisibility directly. It uses the conserving
family to explain the arithmetic, without claiming that an empirically
best ordering has been proved optimal.
'''
head=head.replace('@@D3@@',config['delta3']).replace('@@D4@@',config['delta4'])
parts=[head,(WORK/'arithmetic/readout_and_baseline.tex').read_text(),(WORK/'carry_section.tex').read_text(),(WORK/'arithmetic/broad_shell.tex').read_text()]
if config['extra_tex']:parts.append((ROOT/config['extra_tex']).read_text())
conclusion=r'''
\section{The divisor density and the reduced denominator}
Define $G_n$ by taking the baseline exponents $g(n/p)$ from (G), and the
additional certified shell exponents, at the eligible primes (E).
The preceding arguments prove
\[
 \frac{6C_nd_{19n}^3}{G_n}(Q_n,P_{3,n})\in\Z^2,
 \qquad
 \frac{6C_nd_{19n}^4}{G_n}(Q_n,P_{3,n},P_{4,n})\in\Z^3.
 \tag{I}
\]
For $B\ne0$, form the integer numerator $AP_{3,n}+BP_{4,n}$ in the second
normalization. For $B=0$, use the first one. Consequently the reduced
denominator actually divides the absolute value of the corresponding
integer multiple of $Q_n$. This is why the argument estimates the
reduced denominator, not the height of an unreduced matrix entry.

By the prime number theorem, the baseline logarithmic density is
\[
 \gamma_0=\int_0^\infty\frac{g(x)}{x^2}\,dx
 =6+\sum_{(a,b,m)}m\sum_{t=0}^\infty
       \left(\frac1{t+a}-\frac1{t+b}\right),
\]
where $(a,b,m)$ ranges over the nonzero intervals of $\psi$ in the
appendix. The initial $6$ is the integral of $h_0(x)/x^2$.
Summing the positive rational terms for $0\le t<1000$ gives, exactly,
\[
 \gamma_0>26.2366642995124>26.2366642995.
\]
The omitted tail is between $0$ and $3/1000$. This is a rational
inequality checked by \texttt{certify\_density.py}; it is not a numerical
prime-density fit. Primes dividing $n$ contribute $O(\log n)$, and primes
below $\sqrt{30n}$ contribute $o(n)$, so the eligibility restrictions do
not change this density.
The additional shell density is $@@EXTRA@@$, hence
\[
 \liminf\frac{\log G_n}{n}>@@GAMMA@@.
\]
Since $\log d_{19n}=19n+o(n)$ and
$\log C_n=30n\log(3/2)+o(n)$, (I) gives
\[
 \limsup\frac{\log q_N(A,0)}n
       <122.451536565866-@@GAMMA@@,
\]
\[
 \limsup\frac{\log q_N(A,B)}n
       <141.451536565866-@@GAMMA@@\qquad(B\ne0).
\]
Combining these upper bounds with the accepted error exponent
$E>112.807539247454$ proves the theorem by $\delta\ge E/H-1$.
The fixed factors $6,A,B$ contribute no exponential cost. No
irrationality-measure upper bound is asserted: the present conclusion
concerns this approximation sequence and its reduced denominators.

\section{What has and has not been recovered}
At the previously checked depth $N=500$, the actual reduced approximants
had $\delta_N(1,1)=0.0168532791698\ldots$ and
$\delta_N(1,0)=0.2277787154690\ldots$. The proved lower bounds above are
weaker. They explain a positive joint delta and most of the stronger
pure-$\zeta(3)$ arithmetic, but do not identify the exact asymptotic gcd.
In particular, further cancellation suggested by a finite prime sample
is kept out of $G_n$ until it has a uniform proof.

The executable check reconstructs native products, verifies the integer
forms (I), and verifies that the reduced denominator for each tested
coefficient pair divides the certified integer denominator. The checked
values are $n=1,2,3,10,49,99,249,499$, with pairs
$(1,0),(0,1),(1,1),(1,-1),(2,3),(-7,5)$. These checks supplement the
uniform argument and do not replace it. The carry partition is separately
verified using exact rational arithmetic, and the shell proof has an
independent audit.
'''
conclusion=conclusion.replace('@@EXTRA@@',config['extra_density']).replace('@@GAMMA@@',config['gamma'])
parts.append(conclusion)
parts.append((WORK/'rates/literature_context.tex').read_text())
rows=json.loads((OUT/'profiles/density_certificate.json').read_text())['periodic_profile']
parts.append(r'''\appendix
\section{The exact periodic carry table}
The function $\psi$ is zero at rational endpoints (these primes are
excluded by (E)); on each open interval it has the value below.
For every other $x$, equation (G) determines the full baseline exponent.
\begin{center}\small
\begin{tabular}{ccc@{\qquad}ccc}\toprule
$a$&$b$&$\psi$&$a$&$b$&$\psi$\\\midrule
''')
def texfrac(s):
 if '/' in s:
  return s
 return s
half=(len(rows)+1)//2
for i in range(half):
 r=rows[i];s=rows[i+half]if i+half<len(rows)else None
 vals=[texfrac(r['lo']),texfrac(r['hi']),str(r['value'])]+([texfrac(s['lo']),texfrac(s['hi']),str(s['value'])]if s else ['','',''])
 parts.append('&'.join('$'+x+'$'if x else ''for x in vals)+r'\\[0pt]'+'\n')
parts.append(r'''\bottomrule\end{tabular}\end{center}
\section{Reproducible certificates}
The bundle preserves the \texttt{work/} and \texttt{results/} layout.
Run the following from its root, using Python with \texttt{python-flint}
and \texttt{sympy} installed:
\begin{verbatim}
python work/meijerg5255_arithmetic/profiles/exact_chambers.py
python work/meijerg5255_arithmetic/profiles/certify_density.py
python work/meijerg5255_arithmetic/arithmetic/all_shell_cells.py
python work/meijerg5255_arithmetic/verify_certificate.py
python work/meijerg5255_arithmetic/rates/certify_spectral_constants.py
\end{verbatim}
The chamber and density checks themselves use only Python's standard
library and exact fractions. Native multiplication uses rational Flint
matrices. The scripts do not require the archive notebooks.
\end{document}
''')
# Remove an unnecessary mnemonic from the strategy display.
s='\n'.join(parts).replace(r're_\text{end}=rW_ne_0=',r'rW_ne_0=').replace('(with the leftmost expression understood simply as the endpoint scalar)\n','')
(OUT/'meijerg_zeta3_zeta4_arithmetic.tex').write_text(s)
print(OUT/'meijerg_zeta3_zeta4_arithmetic.tex')
