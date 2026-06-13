Methods and Applications of Analysis 6 (2) 1999, pp. 131-146
© 1999 International Press
ISSN 1073-2772

# APPROXIMATIONS OF ORTHOGONAL POLYNOMIALS IN TERMS OF HERMITE POLYNOMIALS

José L. López and Nico M. Temme

Dedicated to Professor Richard Askey on the occasion of his 65th birthday.

ABSTRACT. Several orthogonal polynomials have limit forms in which Hermite polynomials show up. Examples are limits with respect to certain parameters of the Jacobi and Laguerre polynomials. In this paper, we are interested in more details of these limits, and we give asymptotic representations of several orthogonal polynomials in terms of Hermite polynomials. In fact, we give finite exact representations that have an asymptotic character. From these representations, the well-known limits can be derived easily. Approximations of the zeros of the Gegenbauer polynomials $C_n^\gamma(x)$ and Laguerre polynomials $L_n^\alpha(x)$ are derived (for large values of $\gamma$ and $\alpha$, respectively) in terms of zeros of the Hermite polynomials and compared with numerical values. We also consider the Jacobi polynomials and the so-called Tricomi-Carlitz polynomials.

# 1. Introduction

It is well known that the Hermite polynomials

$$
H_n(x) = n! \sum_{k=0}^{\lfloor n/2 \rfloor} \frac{(-1)^k}{k!(n-2k)!} (2x)^{n-2k} \tag{1.1}
$$

play a crucial role in certain limits of the classical orthogonal polynomials. For example, the Gegenbauer polynomials $C_n^\gamma(x)$, which are defined by the generating function

$$
(1 - 2xw + w^2)^{-\gamma} = \sum_{n=0}^{\infty} C_n^\gamma(x) w^n, \quad -1 \leq x \leq 1, \quad |w| &lt; 1, \tag{1.2}
$$

have the well-known limits (cf. [11, pp. 168, 169])

$$
\lim_{\gamma \to \infty} \frac{C_n^\gamma(x)}{C_n^\gamma(1)} = x^n, \tag{1.3}
$$

$$
\lim_{\gamma \to \infty} \gamma^{-n/2} C_n^\gamma(x / \sqrt{\gamma}) = \frac{1}{n!} H_n(x). \tag{1.4}
$$

These limits give insight into the location of the zeros of $C_n^\gamma(x)$ for large values of the order $\gamma$. The first limit shows that the zeros of $C_n^\gamma(x)$ tend to the origin if the order $\gamma$ tends to infinity. The second limit is more interesting; it gives the relation with

Received June 22, 1998.

1991 Mathematics Subject Classification: 33C25, 41A60, 30C15, 41A10.

Key words and phrases: limits of classical orthogonal polynomials, Hermite polynomials, Jacobi polynomials, Gegenbauer polynomials, Laguerre polynomials, Tricomi-Carlitz polynomials, zeros of polynomials.

the Hermite polynomials if the order becomes large and the argument $x$ is properly scaled.

For the Laguerre polynomials, which are defined by the generating function

$(1-w)^{-\alpha-1}e^{-wx/(1-w)}=\sum_{n=0}^{\infty}L_{n}^{\alpha}(x)\,w^{n},\quad\alpha,x\in\mathbb{C},\quad|w|<1,$ (1.5)

similar results are

$\lim_{\alpha\to\infty}\alpha^{-n}L_{n}^{\alpha}(\alpha x)=\frac{(1-x)^{n}}{n!},$ (1.6)
$\lim_{\alpha\to\infty}\alpha^{-n/2}L_{n}^{\alpha}(x\sqrt{\alpha}+\alpha)=\frac{(-1)^{n}\,2^{-n/2}}{n!}\,H_{n}(x/\sqrt{2}).$ (1.7)

This again gives insight into the location of the zeros for large values of the order $\alpha$, and the relation with the Hermite polynomials if the order becomes large and $x$ is properly scaled.

In this paper, we describe the asymptotics that govern the above limits with the Hermite polynomials. We consider large values of orders $\alpha$ and $\gamma$ and obtain asymptotic representations of $C_{n}^{\gamma}(x)$ and $L_{n}^{\alpha}(x)$ from which the above limits can be derived as special cases.

For large values of the degree $n$ and fixed values of the order $\alpha$, the Laguerre polynomials $L_{n}^{\alpha}(x)$ are considered in *[6]*; see also *[13]*. In our present paper, we keep $n$ fixed, and we do not use the complicated analysis of uniform expansions *[9]*. Our results are rather simple to derive and can be considered as first approximations before considering uniform expansions.

We also discuss Tricomi-Carlitz polynomials, which have been considered recently in *[7, 8]*. These polynomials are related to Laguerre polynomials $L_{n}^{\alpha}(x)$ with negative order $\alpha$.

In the following section, we give the principles of the Hermite-type asymptotic approximations used in this paper. In later sections, we give expansions for the Gegenbauer, the Laguerre, the Jacobi, and the Tricomi-Carlitz polynomials. The same method can be used for many other classes of polynomials.

## 2. Expansions in terms of Hermite polynomials

The Hermite polynomials follow from the generating function

$e^{2xw-w^{2}}=\sum_{n=0}^{\infty}\frac{H_{n}(x)}{n!}w^{n},\quad x,w\in\mathbb{C},$ (2.1)

which gives the Cauchy-type integral

$H_{n}(x)=\frac{n!}{2\pi i}\,\int_{\mathcal{C}}e^{2xz-z^{2}}z^{-n-1}\,dz$ (2.2)

where $\mathcal{C}$ is a circle around the origin and the integration is in positive direction.

### 2.1. An expansion in terms of Hermite polynomials

Many special functions satisfy a relation in the form of a generating series, which usually has the form

$F(x,w)=\sum_{n=0}^{\infty}p_{n}(x)\,w^{n}$ (2.3)

where $F$ is a given function, which is analytic with respect to $w$ in a domain that contains the origin, and $p_{n}$ is independent of $w$. Examples are the generating functions given in (1.2), (1.5), and (2.1).

The relation (2.3) gives, for the special function $p_{n}$, the Cauchy-type integral

$p_{n}(x)=\frac{1}{2\pi i}\int_{c}F(x,w)\,\frac{dw}{w^{n+1}}$ (2.4)

where $\mathcal{C}$ is a circle around the origin inside the domain where $F$ is analytic (as a function of $w$).

We write

$F(x,w)=e^{Aw-Bw^{2}}\,f(x,w)$ (2.5)

where $A$ and $B$ do not depend on $w$ and can be chosen arbitrarily. This gives

$p_{n}(x)=\frac{1}{2\pi i}\int_{\mathcal{C}}e^{Aw-Bw^{2}}\,f(x,w)\,\frac{dw}{w^{n+1}}.$ (2.6)

Because $f$ is also analytic (as a function of $w$), we can expand

$f(x,w)=\sum_{k=0}^{\infty}c_{k}w^{k}$ (2.7)

and substitute this in (2.6). By (2.2), the result is the finite expansion

$p_{n}(x)=z^{n}\,\sum_{k=0}^{n}\frac{c_{k}}{z^{k}}\,\frac{H_{n-k}(\zeta)}{(n-k)!},\quad z=\sqrt{B},\quad\zeta=\frac{A}{2\sqrt{B}},$ (2.8)

because terms with $k>n$ do not contribute in the integral in (2.6). The quantities $A$ and $B$ may depend on $x$, and if $B$ happens to be zero for a special $x-$value $x_{0}$, say, we write

$p_{n}(x_{0})=A^{n}\,\sum_{k=0}^{n}\frac{c_{k}}{A^{k}\,(n-k)!}.$ (2.9)

In the examples considered in the following sections, the choice of $A$ and $B$ is based on our requirement that $c_{1}=c_{2}=0$. This happens if we take

$A=p_{1}(x),\quad B=\frac{1}{2}p_{1}^{2}(x)-p_{2}(x),$ (2.10)

and if we assume that $F(x,0)=p_{0}(x)=1$ (which implies $c_{0}=1$). This is easily verified from (2.3) by writing

$\ln[F(x,w)]=p_{1}(x)w+\bigg{[}p_{2}(x)-\frac{1}{2}p_{1}^{2}(x)\bigg{]}w^{2}+\mathcal{O}(w^{3}),\quad w\to 0.$

This choice of $A$ and $B$ makes the matching at the origin of the exponential function in (2.5) with $F(x,w)$ as best as possible.

We will show in later sections that, for several interesting cases, the finite sum in (2.8) gives the desired asymptotic representations, from which well-known limits can be derived. The special choice of $A$ and $B$ is crucial for obtaining asymptotic properties.

##

3. Gegenbauer polynomials

From (1.2), we obtain the following Cauchy-type integral

$C_{n}^{\gamma}(x)=\frac{1}{2\pi i}\int_{\mathcal{C}}\frac{dw}{(1-2xw+w^{2})^{\gamma}\,w^{\alpha+1}}$ (3.1)

where $\gamma$ is a circle around the origin with radius less than unity. Initially, we assume that $x\in(-1,1)$, but later we do not need this restriction. We assume that $(1-2xw+w^{2})^{\gamma}$ assumes real values for real values of $x,w$ and $\gamma$.

We have

$C_{0}^{\gamma}(x)=1,\quad C_{1}^{\gamma}(x)=2\gamma x,\quad C_{2}^{\gamma}(x)=2\gamma(\gamma+1)x^{2}-\gamma.$ (3.2)

Hence, by (2.10),

$A=2x\gamma,\quad B=\gamma(1-2x^{2}).$

It follows that

$C_{n}^{\gamma}(x)=z^{n}\sum_{k=0}^{n}\frac{c_{k}}{z^{k}}\,\frac{H_{n-k}(\zeta)}{(n-k)!}$ (3.3)

where

$z=\sqrt{B}=\sqrt{\gamma(1-2x^{2})},\quad\zeta=\frac{A}{2\sqrt{B}}=\frac{x\gamma}{z}.$

The coefficients follow from (cf. (2.7))

$f(x,w)=e^{-2\gamma xw+\gamma(1-2x^{2})w^{2}}(1-2xw+w^{2})^{-\gamma}=\sum_{k=0}^{\infty}c_{k}w^{k}.$ (3.4)

We have

$c_{0}=1,\quad c_{1}=c_{2}=0,\quad c_{3}=\frac{2}{3}\gamma x(4x^{2}-3),\quad c_{4}=\frac{1}{2}\gamma[1+8x^{2}(x^{2}-1)].$

Higher coefficients follow from the recursion relation

$kc_{k}=2x(k-1)c_{k-1}-(k-2)c_{k-2}+2\gamma x(4x^{2}-3)c_{k-3}+2\gamma(1-2x^{2})c_{k-4}.$ (3.5)

This relation follows from substituting the Maclaurin series of $f$ (see (3.4)) into the differential equation

$(1-2xw+w^{2})\frac{df}{dw}=2\gamma(-3x+4x^{3}+w-2x^{2}w)w^{2}\,f.$

In (3.3), no restrictions on $x$ and $\gamma$ are needed, although $\zeta$ and $1/z$ become infinite if $x^{2}=\frac{1}{2}$; this singularity is removable because of the term $z^{n}$ in front of the series. It follows from (2.9) that, if $x_{0}^{2}=1/2$, we have

$C_{n}^{\gamma}(x_{0})=(2x_{0}\gamma)^{n}\sum_{k=0}^{n}\frac{c_{k}}{(2x_{0}\gamma)^{k}\,(n-k)!}$ (3.6)

where the $c_{k}$ are as in (3.4) and (3.5) with $x=x_{0}$.

##

APPROXIMATION OF ORTHOGONAL POLYNOMIALS

3.1. Asymptotic properties of the expansion (3.3). To verify the asymptotic character of (3.3), we observe that the sequence $\{\Phi_k\}$ with $\Phi_k = c_k / z^k$ has the following (somewhat irregular $^1$) asymptotic structure:

$$
\Phi_k = \mathcal{O}(\gamma^{\lfloor k/3 \rfloor - k/2}), \quad k = 0, 1, 2, \dots, \tag{3.7}
$$

where $\lfloor x \rfloor$ means the integer part of $x$.

More importantly, the successive Hermite polynomials $H_n(\zeta), H_{n-1}(\zeta), \ldots$, in (3.3) are of lower degree with respect to $\gamma$. This means that, using (3.7),

$$
\frac{c_k}{z^k} H_{n-k}(\zeta) = \mathcal{O}(\gamma^{n/2 + \lfloor k/3 \rfloor - k}), \quad \gamma \to \infty.
$$

This gives the asymptotic nature of the terms in (3.3) for large values of $\gamma$, with $x$ and $n$ fixed. We also can estimate the remainder.

Let, for $n_0 = 0,1,\ldots,n$, the remainder $\Delta_{n_0}$ be defined by

$$
\Delta_{n_0} := \gamma^{-n} \left[ C_n^{\gamma}(x) - z^n \sum_{k=0}^{n_0} \frac{c_k}{z^k} \frac{H_{n-k}(\zeta)}{(n-k)!} \right] = \gamma^{-n} z^n \sum_{k=n_0+1}^{n} \frac{c_k}{z^k} \frac{H_{n-k}(\zeta)}{(n-k)!}.
$$

Then we can estimate $\Delta_{n_0}$ for large $\gamma$. For example, for $n = 20$, we have the following results:

$$
n_0 = 0, 1, 2, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-2}),
$$

$$
n_0 = 3, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-3}),
$$

$$
n_0 = 4, 5, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-4}),
$$

$$
n_0 = 6, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-5}),
$$

$$
n_0 = 7, 8, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-6}),
$$

$$
n_0 = 9, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-7}),
$$

$$
n_0 = 10, 11, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-8}),
$$

$$
n_0 = 12, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-9}),
$$

$$
n_0 = 13, 14, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-10}),
$$

$$
n_0 = 15, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-11}),
$$

$$
n_0 = 16, 17, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-12}),
$$

$$
n_0 = 18, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-13}),
$$

$$
n_0 = 19, \quad \Delta_{n_0} = \mathcal{O}(\gamma^{-14}),
$$

$$
n_0 = 20, \quad \Delta_{n_0} = 0.
$$

In fact, we have

$$
\Delta_{n_0} = \mathcal{O}(\gamma^{\lfloor (n_0+1)/3 - n_0 - 1 \rfloor}), \quad \text{as} \quad \gamma \to \infty.
$$

For proofs of the asymptotic properties, we refer to the following subsection.

It is not difficult to verify that the limits given in (1.3) and (1.4) follow from (3.3).

3.2. Proofs of the asymptotic properties

To prove the asymptotic properties of the expansion, we first show that the coefficients $c_{k}$ in formula (3.4) satisfy

$c_{k}=\mathcal{O}(\gamma^{\lfloor k/3\rfloor}),\quad\gamma\to\infty.$ (3.8)

The proof follows by induction with respect to $k$ and by using the recurrence relation (3.5), which we write in the form

$c_{k}=ac_{k-1}+bc_{k-2}+c\gamma c_{k-3}+d\gamma c_{k-4}$ (3.9)

where $a,b,c,d$ are functions of $k$ and $x$, generically different from $0$ ($a\neq 0$ for $x\neq 0$, $b\neq 0$ for all $x$, $c\neq 0$ for $x\neq 0$ and $x\neq\pm\sqrt{3}/2$, and $d\neq 0$ for $x\neq\pm 1/\sqrt{2}$).

(i) From the coefficients given after (3.4), it follows that (3.8) is true for $k=0,1,2,3,4$.

(ii) Suppose that (3.8) is true for a given $k\geq 4$. Then, using (3.9),

$c_{k+1}$ $=a\mathcal{O}(\gamma^{\lfloor k/3\rfloor})+b\mathcal{O}(\gamma^{\lfloor(k-1)/3\rfloor})+c\mathcal{O}(\gamma^{1+\lfloor(k-2)/3\rfloor})+d\mathcal{O}(\gamma^{1+\lfloor(k-3)/3\rfloor})$
$=(a+d)\mathcal{O}(\gamma^{\lfloor k/3\rfloor})+b\mathcal{O}(\gamma^{\lfloor(k-1)/3\rfloor})+c\mathcal{O}(\gamma^{\lfloor(k+1)/3\rfloor})$
$=c\mathcal{O}(\gamma^{\lfloor(k+1)/3\rfloor}).$

Therefore, (3.8) is proved, and by using $\Phi_{k}=c_{k}/z^{k}$ and $z=\mathcal{O}(\gamma^{1/2})$, it follows that (3.7) holds true.

The above derivation fails when $c=0$. However, the estimate of the order in $\gamma$ can be improved when $c=0$. That is, when $x=0$ or $x=\pm\sqrt{3}/2$, we can show

$c_{k}=\mathcal{O}(\gamma^{\lfloor k/4\rfloor}).$ (3.10)

In this case, the recurrence (3.5) reads

$c_{k}=ac_{k-1}+bc_{k-2}+d\gamma c_{k-4},$ (3.11)

(where $a$ is also zero if $x=0$). We can repeat the steps (i), (ii) in the above induction proof:

(i) (3.10) is true for $k=0,1,2,3,4$ ($c_{3}=0$ for $x=0$ or $x=\pm\sqrt{3}/2$).

(ii) Suppose (3.10) is true for $k\geq 4$. Then,

$c_{k+1}$ $=a\mathcal{O}(\gamma^{\lfloor k/4\rfloor})+b\mathcal{O}(\gamma^{\lfloor(k-1)/4\rfloor})+d\mathcal{O}(\gamma^{1+\lfloor(k-3)/4\rfloor})$
$=a\mathcal{O}(\gamma^{\lfloor k/4\rfloor})+b\mathcal{O}(\gamma^{\lfloor(k-1)/4\rfloor})+d\mathcal{O}(\gamma^{\lfloor(k+1)/4\rfloor})$
$=d\mathcal{O}(\gamma^{\lfloor(k+1)/4\rfloor}).$

And so, (3.10) is proved. Therefore, for $c=0$,

$\Phi_{k}=\mathcal{O}(\gamma^{\lfloor k/4\rfloor-k/2}),\quad k=0,1,2,\dots.$ (3.12)

This derivation of (3.10) fails when $d=0$. But in this case $c\neq 0$ and (3.7) holds.

### 3.3. Approximating the zeros

When computing approximations of the zeros of the Gegenbauer polynomials for large values of $\gamma$, we start with the zeros of the Hermite polynomial $H_{n}(\zeta)$ in (3.3).

Let $g_{n,m}$, $h_{n,m}$, $m=1,2,\dots,n$, be the $m$th zero of $C_{n}^{\gamma}(x)$, $H_{n}(x)$, respectively. Then, for given $\gamma$ and $n$, we take the relation for $\zeta$ used in (3.3) to compute a first approximation of $g_{n,m}$ by writing

$\frac{\gamma g_{n,m}}{\sqrt{\gamma(1-2g_{n,m}^{2})}}\sim h_{n,m}.$

###

Inverting this relation, we obtain

$g_{n,m}\sim\frac{h_{n,m}}{\sqrt{\gamma+2h_{n,m}^{2}}},\quad m=1,2,\ldots,n.$ (3.13)

The accuracy is rather limited, unless $\gamma$ is very large. For example, if $\gamma=1000$, $n=20$, the best relative accuracy in the zeros is about $1/1000$, but the worst result (for the largest zero) is $0.016$. In the next section, we give more details on how to obtain better approximations from the representation like (3.3) for the case of the Laguerre polynomials.

## 4. Laguerre polynomials

We take

$F(x,w)=(1+w)^{-\alpha-1}e^{wx/(1+w)}=\sum_{n=0}^{\infty}p_{n}(x)\,w^{n}$ (4.1)

as the generating function (see (1.5)) with

$p_{n}(x)=(-1)^{n}L_{n}^{\alpha}(x).$ (4.2)

We have

$L_{0}^{\alpha}(x)=1,\quad L_{1}^{\alpha}(x)=\alpha+1-x,\quad L_{2}^{\alpha}(x)=\frac{1}{2}[(\alpha+1)(\alpha+2)-2(\alpha+2)x+x^{2}].$

This gives

$A=x-\alpha-1,\quad B=x-\frac{1}{2}(\alpha+1).$

Writing

$f(x,w)=F(x,w)\,e^{-Aw+Bw^{2}}=\sum_{k=0}^{\infty}c_{k}w^{k},$ (4.3)

we obtain

$c_{0}=1,\quad c_{1}=c_{2}=0,\quad c_{3}=\frac{1}{3}(3x-\alpha-1),\quad c_{4}=\frac{1}{4}(-4x+\alpha+1),$

and the recursion relation

$kc_{k}=-2(k-1)c_{k-1}-(k-2)c_{k-2}+(3x-\alpha-1)c_{k-3}+(2x-\alpha-1)c_{k-4}.$ (4.4)

This relation follows from substituting the Maclaurin series of $f$ into the differential equation

$(1+w)^{2}\,\frac{df}{dw}=\left[3x-\alpha-1+(2x-1-a)w\right]w^{2}\,f.$

It follows that

$L_{n}^{\alpha}(x)=(-1)^{n}\,z^{n}\,\sum_{k=0}^{n}\,\frac{c_{k}}{z^{k}}\,\frac{H_{n-k}(\zeta)}{(n-k)!}$ (4.5)

where

$z=\sqrt{x-(\alpha+1)/2},\quad\zeta=\frac{x-\alpha-1}{2z}.$ (4.6)

The representation in (4.5) holds for $n=0,1,2,\dots$, and all complex values of $x$ and $\alpha$. If $z=0$, it is more convenient to write

$L_{n}^{\alpha}(x_{0})=x_{0}^{n}\sum_{k=0}^{n}\frac{(-1)^{k}\,c_{k}}{x_{0}^{k}\,(n-k)!}$

where the $c_{k}$ are determined from (4.3) and (4.4), with $x=x_{0}=\frac{1}{2}(\alpha+1)$.

The representation in (4.5) has an asymptotic character for large values of $|\alpha|+|x|$; the degree $n$ should be fixed. To verify the asymptotic character, we write $\gamma=\alpha+1$, $x=\gamma\xi$. We observe that the sequence $\{\Phi_{k}\}$ with $\Phi_{k}=c_{k}/z^{k}$ has the following asymptotic structure:

$\Phi_{k}=\mathcal{O}[\gamma^{-\lfloor k/3\rfloor-k/2}],\quad k=0,1,2,\dots,$ (4.7)

as $\gamma\to\infty$. The derivation of (4.7) runs as in the case of the Gegenbauer polynomials (Section 3.1). The only difference is that, in this case in the recurrence relation (3.9), we have $c=3\xi-1$ and $d=2\xi-1$. Therefore, condition $c\neq 0$ reads $\xi\neq 1/3$ and $d\neq 0$ reads $\xi\neq 1/2$. Also, in this case, $a$ never vanishes.

Again, the successive Hermite polynomials $H_{n}(\zeta),H_{n-1}(\zeta),\dots$, in (4.5) are of lower degree with respect to $\gamma$. This, together with (4.7), explains the asymptotic nature of the representation in (4.4) for large values of $|\alpha|+|x|$, with $n$ fixed.

It is not difficult to verify that the limits given in (1.6) and (1.7) follow from (4.5).

### 4.1. Approximating the zeros

Let $l_{n,m}$, $h_{n,m}$, $m=1,2,\dots,n$, be the $m$th zero of $L_{n}^{\alpha}(x),H_{n}(x)$, respectively. Then, for given $\alpha$ and $n$, we use the relation for $\zeta$ in (4.6) to compute a first approximation of $l_{n,m}$ by writing

$\frac{l_{n,m}-\alpha-1}{2\sqrt{l_{n,m}-\frac{1}{2}(\alpha+1)}}\sim h_{n,m}.$

Inverting this relation, we obtain

$l_{n,m}\sim\alpha+1+2h_{n,m}^{2}+h_{n,m}\sqrt{2(\alpha+1)+4h_{n,m}^{2}}\ .$ (4.8)

In *[3]*, the following asymptotic result has been given:

$l_{n,m}=\alpha+\sqrt{2\alpha}h_{n,m}+\frac{1}{3}(1+2n+2h_{n,m}^{2})+\mathcal{O}\big{(}\alpha^{-\frac{1}{2}}\big{)},$ (4.9)

as $\alpha\to\infty$. This result does not follow from (4.8), but we can derive (4.9) from (4.5). We give a few steps of this method.

Using the recursion relations

$2nH_{n-1}(x)=2xH_{n}(x)-H_{n+1}(x)=\frac{d}{dx}H_{n}(x),$

we obtain

$H_{n-3}(\zeta)=\frac{1}{4n(n-1)(n-2)}[(2\zeta^{2}-n+1)H_{n}^{\prime}(\zeta)-2\zeta nH_{n}(\zeta)].$ (4.10)

Hence, the first two nonvanishing terms in (4.5) yield

$\frac{1}{n!}H_{n}(\zeta)+\frac{c_{3}}{(n-3)!z^{3}}H_{n-3}(\zeta)=\frac{1}{n!}[F(\zeta)H_{n}(\zeta)+G(\zeta)H_{n}^{\prime}(\zeta)]$ (4.11)

where

$F(\zeta)=1-\frac{\zeta nc_{3}}{2z^{3}},\quad G(\zeta)=\frac{c_{3}(2\zeta^{2}-n+1)}{4z^{3}},$

with $c_{3}$ given after (4.3); $x$ can be written as a function of $\zeta$ by inverting the relations used in (4.6), that is,

$x=\alpha+1+2\zeta^{2}+\zeta\sqrt{2(\alpha+1)+4\zeta^{2}}.$ (4.12)

Now, let $h$ be a zero of $H_{n}(\zeta)$. To solve $F(\zeta)H_{n}(\zeta)+G(\zeta)H_{n}^{\prime}(\zeta)=0$, we substitute $\zeta=h+\varepsilon$ and expand in powers of $\varepsilon$. Neglecting powers $\varepsilon^{n},n\geq 2$, we obtain

$[G(h)+\varepsilon\{F(h)+G^{\prime}(h)\}]H_{n}^{\prime}(h)+\varepsilon G(h)H_{n}^{\prime\prime}(h)$
$=[G(h)+\varepsilon\{F(h)+G^{\prime}(h)+2hG(h)\}]H_{n}^{\prime}(h)\sim 0$

where we have replaced $H_{n}^{\prime\prime}(h)$ with $2hH_{n}^{\prime}(h)$ by using the differential equation of the Hermite polynomials.

Solving for $\varepsilon$, we find

$\varepsilon\sim\frac{-G(h)}{F(h)+G^{\prime}(h)+2hG(h)},$

and, expanding the result for large $\alpha$, we obtain

$\varepsilon=\frac{1}{3}\sqrt{\frac{2}{\alpha}}(n-1-2h^{2})+\mathcal{O}(\alpha^{-1}).$ (4.13)

Substituting $\zeta=h+\varepsilon$ with the approximation (4.13) in (4.12) and expanding again, we find

$x=\alpha+\sqrt{2\alpha}h+\frac{1}{3}(1+2n+2h^{2})+\mathcal{O}(\alpha^{-\frac{1}{2}}),\quad\alpha\to\infty,$

which is the same as Calogero’s result (4.9).

In Table 1, for $n=10$, we show the relative accuracy in the approximation (4.9) for several values of $\alpha$. That is, we show

$\left|\frac{l_{10,m}-\widetilde{l}_{10,m}}{l_{10,m}}\right|,\quad m=1,2,\ldots,10,$

where $\widetilde{l}_{10,m}$ are the approximations obtained by (4.9).

## 5 The Tricomi-Carlitz polynomials

The Tricomi-Carlitz polynomials are defined by

$t_{n}^{(\alpha)}(x)=\sum_{k=0}^{n}(-1)^{k}\binom{x-\alpha}{k}\frac{x^{n-k}}{(n-k)!}.$ (5.1)

We have the relation with the Laguerre polynomials:

$t_{n}^{(\alpha)}(x)=(-1)^{n}\,L_{n}^{(x-\alpha-n)}(x).$ (5.2)

The polynomials satisfy the recurrence relation

$(n+1)t_{n+1}^{(\alpha)}(x)-(n+\alpha)\,t_{n}^{(\alpha)}(x)+x\,t_{n-1}^{(\alpha)}(x)=0,\quad n\geq 1,$ (5.3)

LOPEZ AND TEMME

|  m | α | 10 | 50 | 100 | 250 | 500 | 1000  |
| --- | --- | --- | --- | --- | --- | --- | --- |
|  1 |  | .17e+1 | .11e-0 | .35e-1 | .77e-2 | .25e-2 | .84e-3  |
|  2 |  | .73e-0 | .63e-1 | .21e-1 | .49e-2 | .16e-2 | .56e-3  |
|  3 |  | .34e-0 | .36e-1 | .12e-1 | .30e-2 | .10e-2 | .36e-3  |
|  4 |  | .15e-0 | .18e-1 | .65e-2 | .16e-2 | .57e-3 | .20e-3  |
|  5 |  | .40e-1 | .54e-2 | .20e-2 | .52e-3 | .18e-3 | .64e-4  |
|  6 |  | .25e-1 | .41e-2 | .16e-2 | .45e-3 | .17e-3 | .60e-4  |
|  7 |  | .67e-1 | .12e-1 | .48e-2 | .13e-2 | .50e-3 | .18e-3  |
|  8 |  | .95e-1 | .18e-1 | .77e-2 | .22e-2 | .83e-3 | .31e-3  |
|  9 |  | .12e-0 | .24e-1 | .11e-1 | .31e-2 | .12e-2 | .45e-3  |
|  10 |  | .13e-0 | .31e-1 | .14e-1 | .42e-2 | .16e-2 | .62e-3  |

TABLE 1. Relative accuracy in computed zeros of  ${L}_{10}^{\alpha }\left( x\right)$  by using approximation (4.9).

with initial values  $t_0^{(\alpha)}(x) = 1$ ,  $t_1^{(\alpha)}(x) = \alpha$ . A few other values are

$$
t _ {2} ^ {(\alpha)} (x) = \frac {1}{2} (\alpha + \alpha^ {2} - x), \quad t _ {3} ^ {(\alpha)} (x) = \frac {1}{6} (2 \alpha + 3 \alpha^ {2} + \alpha^ {3} - 2 x - 3 x \alpha). \tag {5.4}
$$

Tricomi [12] introduced the polynomials. He observed that  $\{t_n^{(\alpha)}(x)\}$  is not a system of orthogonal polynomials, the recurrence relations failing to have the required form (cf. [10, page 43]). However, [2] discovered that if one sets

$$
f _ {n} ^ {(\alpha)} (x) = x ^ {n} t _ {n} ^ {(\alpha)} \left(x ^ {- 2}\right), \tag {5.5}
$$

then  $\{f_n^{(\alpha)}(x)\}$  satisfies

$$
(n + 1) f _ {n + 1} ^ {(\alpha)} (x) - (n + \alpha) x f _ {n} ^ {(\alpha)} (x) + f _ {n - 1} ^ {(\alpha)} (x) = 0, \quad n \geq 1, \tag {5.6}
$$

with initial values  $f_0^{(\alpha)}(x) = 1$ ,  $f_1^{(\alpha)}(x) = \alpha x$ . A few other values are

$$
f _ {2} ^ {(\alpha)} (x) = \frac {1}{2} [ \alpha (1 + \alpha) x ^ {2} - 1 ], \quad f _ {3} ^ {(\alpha)} (x) = \frac {1}{6} x \left(- 2 + 2 \alpha x ^ {2} - 3 \alpha + 3 \alpha^ {2} x ^ {2} + \alpha^ {3} x ^ {2}\right).
$$

There is a generating function for  $f_{n}^{(\alpha)}(x)$ :

$$
F (x, w) = e ^ {w / x + \left(1 - \alpha x ^ {2}\right) / x ^ {2} \ln (1 - x w)} = \sum_ {n = 0} ^ {\infty} f _ {n} ^ {(\alpha)} (x) w ^ {n}, \quad | w x | &lt;   1. \tag {5.7}
$$

If  $x = 0$ , this reduces to

$$
e ^ {- \frac {1}{2} w ^ {2}} = \sum_ {n = 0} ^ {\infty} f _ {2 n} ^ {(\alpha)} (0) w ^ {2 n},
$$

giving

$$
f _ {2 n} ^ {(\alpha)} (0) = (- 1) ^ {n} 2 ^ {- n} / n!, \quad f _ {2 n + 1} ^ {(\alpha)} (0) = 0, \quad n = 0, 1, 2, \ldots .
$$

Carlitz proved that for  $\alpha &gt; 0$ ,  $\{f_n^{(\alpha)}(x)\}$  satisfies the orthogonality relation

$$
\int_ {- \infty} ^ {\infty} f _ {m} ^ {(\alpha)} f _ {n} ^ {(\alpha)} (x) d \psi^ {(\alpha)} (x) = \frac {2 e ^ {\alpha}}{(n + \alpha) n !} \delta_ {m n} \tag {5.8}
$$

where $\psi^{(\alpha)}(x)$ is the step function whose jumps are

$d\,\psi^{(\alpha)}(x)=\frac{(k+\alpha)^{k-1}\,e^{-k}}{k!}\quad\text{at}\quad x=x_{k}=\pm\frac{1}{\sqrt{k+\alpha}},\quad k=0,1,2,\ldots.$ (5.9)

The values $x_{k}$ play a special role in the generating function because for these $x$-values, we have

$e^{w/x_{k}}\,(1-x_{k}w)^{k}=\sum_{n=0}^{\infty}\,f_{n}^{(\alpha)}(x_{k})\,w^{n},$

and now the series converges for all values of $w$.

For further generalizations of the Tricomi-Carlitz polynomials, the reader is referred to *[1]* and *[5]*; *[4]* gives a brief treatment of the polynomials $t_{n}^{(\alpha)}(x)$. Goh and Wimp *[7, 8]* establish the asymptotic behavior of the Tricomi-Carlitz polynomials and discuss their distribution of zeros. They observe that the polynomials $f_{n}(x/\sqrt{\alpha}\,)$ have all zeros in the interval $[-1,1]$. They use, in their second paper, a probabilistic approach for improving their earlier results concerning the asymptotic distribution of the zeros of the polynomials $f_{n}^{(\alpha)}(x)$. Saddle point methods are used to study the asymptotics for $f_{n}^{(\alpha)}(x)$ in the complex plane.

In this section, we use the method of Section 2 for obtaining an asymptotic representation (for large values of $\alpha$) of the Tricomi-Carlitz polynomials in terms of the Hermite polynomial.

The role of the Hermite polynomials can be shown by observing that

$\lim_{\alpha\to\infty}f_{n}^{(\alpha)}\bigg{(}\frac{x\sqrt{2}}{\alpha}\bigg{)}=\frac{2^{-n/2}}{n!}\,H_{n}(x).$ (5.10)

This follows from the results given below.

### 5.1. Hermite-type representation of the Tricomi-Carlitz polynomials

From the first polynomials given after (5.6), we obtain

$A=\alpha x,\quad B=\frac{1}{2}(1-\alpha x^{2}).$

Hence,

$f_{n}^{(\alpha)}(x)=z^{n}\,\sum_{k=0}^{n}\frac{c_{k}}{z^{k}}\,\frac{H_{n-k}(\zeta)}{(n-k)!}$ (5.11)

where

$z=\sqrt{(1-\alpha x^{2})/2},\quad\zeta=\frac{\alpha x}{\sqrt{2(1-\alpha x^{2})}}.$

For the special value $x=x_{0}$ that satisfies $\alpha x_{0}^{2}=1$, it is better to write an expansion of the form (2.9).

The coefficients $c_{k}$ in (5.11) are defined by

$f(x,w)=F(x,w)\,e^{-Aw+Bw^{2}}=\sum_{k=0}^{\infty}c_{k}w^{k}$

where $F(x,w)$ is given in (5.7). We have

$c_{0}=1,\quad c_{1}=c_{2}=0,\quad c_{3}=\frac{1}{3}x(\alpha x^{2}-1),\quad c_{4}=\frac{1}{4}x^{2}(1-\alpha x^{2}).$

The coefficients can be computed easily from the differential equation

$(xw-1)\frac{df}{dw}=x(1-\alpha x^{2})w^{2}\,f,$

which gives the recursion relation

$kc_{k}=x(k-1)c_{k-1}+x(\alpha x^{2}-1)c_{k-3},\quad k=3,4,\dots.$ (5.12)

Observe that $c_{0}=f(0,w)=1$, and that $c_{k}=0$, $k\geq 1$ if $x=0$.

To verify the asymptotic character of (5.11), we observe that the sequence $\{\Phi_{k}\}$ with $\Phi_{k}:=c_{k}/z^{k}$ has the following asymptotic structure:

$\Phi_{k}=\mathcal{O}[\alpha^{-\lfloor k/3\rfloor-k/2}],\quad k=0,1,2,\dots,$

as $\alpha\to\infty$, $x\neq 0$. The main step in verifying this estimate is the proof of

$c_{k}=\mathcal{O}(\alpha^{\lfloor k/3\rfloor}),\quad\alpha\to\infty,$

which follows from (5.12) and the fact that the successive Hermite polynomials $H_{n}(\zeta)$, $H_{n-1}(\zeta),\dots$, in (5.11) are of lower degree with respect to $\alpha$. This explains the asymptotic nature of the representation in (5.11) for large values of $\alpha$, with $x\neq 0$ and $n$ fixed.

Observe that the limit in (5.10) indeed follows from (5.11).

### 5.2. Approximating the zeros

Let $f_{n,m}$, $h_{n,m}$, $m=1,2,\dots,n$, be the $m$th zero of $L_{n}^{\alpha}(x),H_{n}(x)$, respectively. Then, for given $\alpha$ and $n$, we use the relation for $\zeta$ in (5.11) to compute a first approximation of $f_{n,m}$ by writing

$\frac{\alpha f_{n,m}}{\sqrt{2(1-\alpha f_{n,m}^{2})}}\sim h_{n,m}.$

Inverting this relation, we obtain

$f_{n,m}\sim h_{n,m}\sqrt{\frac{2}{\alpha^{2}+2\alpha h_{n,m}^{2}}}\ .$ (5.13)

We can use the method of §4.1 for obtaining better approximations.

## 6. Jacobi polynomials

We give a few steps for the Jacobi case, which is quite complicated because of the many parameters involved. Consider the generating function

$F(x,w)=\frac{2^{\alpha+\beta}}{R}(1-w+R)^{-\alpha}(1+w+R)^{-\beta}=\sum_{n=0}^{\infty}P_{n}^{(\alpha,\beta)}(x)w^{n}$ (6.1)

where

$R=\sqrt{1-2xw+w^{2}}.$

We have

$P_{0}^{(\alpha,\beta)}(x)=1,$
$P_{1}^{(\alpha,\beta)}(x)=\frac{1}{2}\big{[}\alpha-\beta+(\alpha+\beta+2)x\big{]},$
$P_{2}^{(\alpha,\beta)}(x)=\frac{1}{8}\big{\{}(1+\alpha)(2+\alpha)+(1+\beta)(2+\beta)-2(\alpha+2)(\beta+2)$
$\qquad+2x[(1+\alpha)(2+\alpha)-(1+\beta)(2+\beta)]$
$\qquad+x^{2}[(1+\alpha)(2+\alpha)+(1+\beta)(2+\beta)+2(\alpha+2)(\beta+2)]\big{\}},$

from which $A$ and $B$ follow:

$A=\frac{1}{2}\big{[}\alpha-\beta+(\alpha+\beta+2)x\big{]},$
$B=\frac{1}{8}\big{[}\alpha+\beta+4+2x(\beta-\alpha)-x^{2}(3\alpha+3\beta+8)\big{]}.$ (6.2)

We obtain the expansion

$P_{n}^{(\alpha,\beta)}(x)=z^{n}\sum_{k=0}^{n}\frac{c_{k}}{z^{k}}\frac{H_{n-k}(\zeta)}{(n-k)!}$ (6.3)

where

$z=\sqrt{B},\quad\zeta=\frac{A}{2\sqrt{B}},$ (6.4)

and $c_{k}$ are the coefficients defined by

$f(x,w)=F(x,w)e^{-Aw+Bw^{2}}=\sum_{k=0}^{\infty}c_{k}w^{k},$ (6.5)

with $F(x,w)$ given in (6.1). We have

$c_{0}=1,\qquad c_{1}=c_{2}=0,$
$c_{3}=\frac{1}{12}[\beta-\alpha-3x(\alpha+\beta+4)+3x^{2}(\alpha-\beta)+x^{3}(5\alpha+5\beta+16)].$ (6.6)

For large values of the parameters $\alpha$ and $\beta$, we can prove that the quantities $\Phi_{k}:=c_{k}/z^{k}$ have the asymptotic behavior as shown in (3.7).

The following limit is of interest:

$\lim_{\alpha,\beta\to\infty}\Big{(}\frac{8}{\alpha+\beta}\Big{)}^{n/2}\ P_{n}^{(\alpha,\beta)}\Big{(}x\sqrt{\frac{2}{\alpha+\beta}}-\frac{\alpha-\beta}{\alpha+\beta}\Big{)}=\frac{1}{n!}\,H_{n}(x),$ (6.7)

under the conditions that

$\frac{\alpha-\beta}{\alpha+\beta}=o(1),\qquad x={\cal O}(1),\qquad\mbox{as}\quad\alpha,\beta\to\infty.$ (6.8)

Details on this limit will be given in the next section. Graphs of the polynomials of (6.7) (with $\alpha=50,\beta=40$) are given in Figure 1.

LOPEZ AND TEMME

![img-0.jpeg](img-0.jpeg)
FIGURE 1. Graphs of the Hermite and Jacobi polynomials that occur in (6.7) (with  $\alpha = 50, \beta = 40$ ). The graphs coincide when  $\alpha, \beta \to \infty$ .

6.1. Asymptotic properties of the expansion (6.3). We want to show formula (3.8) for the Jacobi case. It is very similar to the other cases, although somewhat more complicated.

We can derive a linear second order differential equation  $pf'' + qf' + rf = 0$  (where derivatives are with respect to  $w$ ) of the function  $f(x, w)$  defined in (6.5). The quantities  $p, q$ , and  $r$  are polynomials in  $\alpha, \beta, x$ , and  $w$ , and are available on request from the authors (together they fill several pages of Maple output). They have the following structure

$$
p = \sum_ {k = 1} ^ {4} p _ {k} w ^ {k}, \quad q = \sum_ {k = 0} ^ {5} q _ {k} w ^ {k}, \quad r = \sum_ {k = 2} ^ {6} r _ {k} w ^ {k}.
$$

Let  $\gamma = \max (\alpha ,\beta)$ . From the Maple output, we observe that, for all values of the index  $k$ ,

$$
p _ {k} = \mathcal {O} (\gamma), \qquad q _ {k} = \mathcal {O} (\gamma^ {2}), \qquad r _ {k} = \mathcal {O} (\gamma^ {3}).
$$

By substituting this information into the differential equation  $pf'' + qf' + rf = 0$ , we obtain, for the coefficients  $c_k$  of (6.5), a recurrence relation of the form

$$
c _ {k + 1} = a c _ {k} + b c _ {k - 1} + c c _ {k - 2} + d c _ {k - 3} + e c _ {k - 4} + f c _ {k - 5} + g c _ {k - 6}. \tag {6.9}
$$

We denote  $h \equiv (k + 1)(kp_1 + q_0) = \mathcal{O}(\gamma^2)$ . Then, we have

$$
a = \frac {k ((k - 1) p _ {2} + q _ {1})}{h} = \mathcal {O} (1), \quad b = \frac {(k - 1) ((k - 2) p _ {3} + q _ {2})}{h} = \mathcal {O} (1),
$$

$$
c = \frac {(k - 2) (k - 3) p _ {4} + (k - 2) q _ {3} + r _ {2}}{h} = \mathcal {O} (\gamma), \quad d = \frac {(k - 3) q _ {4} + r _ {3}}{h} = \mathcal {O} (\gamma),
$$

$$
e = \frac {(k - 4) q _ {5} + r _ {4}}{h} = \mathcal {O} (\gamma), \quad f = \frac {r _ {5}}{h} = \mathcal {O} (\gamma), \quad g = \frac {r _ {6}}{h} = \mathcal {O} (\gamma).
$$

For the first four  $c_k$ , we have (cf. (6.6))

$$
c _ {0} = 1 = \mathcal {O} (1), \quad c _ {1} = c _ {2} = 0 = \mathcal {O} (1), \quad c _ {3} = \mathcal {O} (\gamma).
$$

By computing the next coefficients, we find that

$c_{4}=-(r_{3}+3q_{1}c_{3}+6p_{2}c_{3})/(12p_{1}+4q_{0})=\mathcal{O}(\gamma),$

and similarly

$c_{5}=\mathcal{O}(\gamma),\quad c_{6}=\mathcal{O}(\gamma^{2}),\quad c_{7}=\mathcal{O}(\gamma^{2}).$

Therefore, equation (3.8) holds for $k=0,\ldots,7$. Now let us suppose that (3.8) holds for a certain $k\geq 7$. Then, using the recurrence relation (6.9) and the orders of $a,\ldots,g$, we have

$c_{k+1}$ $=a\mathcal{O}(\gamma^{\lfloor k/3\rfloor})+b\mathcal{O}(\gamma^{\lfloor(k-1)/3\rfloor})+\frac{c}{\gamma}\mathcal{O}(\gamma^{1+\lfloor(k-2)/3\rfloor})+\frac{d}{\gamma}\mathcal{O}(\gamma^{1+\lfloor(k-3)/3\rfloor})$
$\qquad+\frac{c}{\gamma}\mathcal{O}(\gamma^{1+\lfloor(k-4)/3\rfloor})+\frac{f}{\gamma}\mathcal{O}(\gamma^{1+\lfloor(k-5)/3\rfloor})+\frac{g}{\gamma}\mathcal{O}(\gamma^{1+\lfloor(k-6)/3\rfloor})$
$=\frac{c}{\gamma}\mathcal{O}(\gamma^{\lfloor(k+1)/3\rfloor})$
$=\mathcal{O}(\gamma^{\lfloor(k+1)/3\rfloor}),$

unless $c=0$. But, for generic $x$, $c\neq 0$. The order of $c$ is governed by $r_{2}$, which is a polynomial of degree $3$ in $x$ that vanishes, at most, for three real values of $x$. For the real roots of $r_{2}$, the order (3.8) of $c_{k}$ could be improved as in the other cases. Details on these special cases will not be given because they are not essential.

We conclude with giving details on the limit in (6.7). For large $\alpha$ and $\beta$, the quantities $A$ and $B$ of (6.2) behave as follows:

$A\sim\frac{1}{2}\left(\alpha+\beta\right)(x+\rho),\quad B\sim\frac{1}{8}\left(\alpha+\beta\right)(1+2x\rho-3x^{2}),\quad\rho=\frac{\alpha-\beta}{\alpha+\beta}.$ (6.10)

Hence,

$z\sim\sqrt{\frac{\alpha+\beta}{8}}\,\sqrt{1+2x\rho-3x^{2}},\quad\zeta\sim\sqrt{\frac{\alpha+\beta}{2}}\,\frac{\rho+x}{\sqrt{1+2x\rho-3x^{2}}}.$ (6.11)

If $x\rho$ and $x^{2}$ become small for large values of $\alpha$ and $\beta$, we can easily invert the relation between $\zeta$ and $x$, giving

$x\sim\sqrt{\frac{2}{\alpha+\beta}}\,\zeta-\rho,\quad z\sim\sqrt{\frac{\alpha+\beta}{8}}.$ (6.12)

Hence, taking only the term $k=0$ in (6.3), we obtain

$P_{n}^{(\alpha,\beta)}\biggl{(}\sqrt{\frac{2}{\alpha+\beta}}\,\zeta-\frac{\alpha-\beta}{\alpha+\beta}\biggr{)}\sim\biggl{(}\frac{\alpha+\beta}{8}\biggr{)}^{n/2}\frac{H_{n}(\zeta)}{n!},\quad\text{as}\quad\alpha,\beta\to\infty.$ (6.13)

Replacing $x$ and $\zeta$, we obtain (6.7) under the conditions given in (6.8). We can relax this condition and derive more complicated limits. But the simple form of (6.7) is rather attractive and will get lost under more general conditions on $x$ and $\alpha-\beta$.

Again, an approximation of the zeros $j_{n,m}$ of $P_{n}^{(\alpha,\beta)}$ follows from (6.13):

$j_{n,m}\sim\sqrt{\frac{2}{\alpha+\beta}}\,h_{n,m}-\frac{\alpha-\beta}{\alpha+\beta},\quad m=1,2,\ldots,n,$

where $h_{n,m}$ are the zeros of $H_{n}(\zeta)$. When we use the method of §4.1, we obtain the following:

$j_{n,m}=-\frac{\alpha-\beta}{\alpha+\beta}+\frac{2\sqrt{2\alpha\beta}h_{n,m}}{(\alpha+\beta)^{\frac{1}{2}}}+\frac{2(\alpha-\beta)(2n+1+2h_{n,m}^{2})}{(\alpha+\beta)^{2}}+\mathcal{O}(\alpha^{-\frac{3}{2}}),$ (6.14)

LOPEZ AND TEMME

for $m=1,2,\ldots,n$. This expansion is derived under the conditions $\alpha\to\infty$, $\beta=b\alpha$, $b$ fixed, and not with the approximations given in (6.10)–(6.12), but by using the original values of $A$, $B$, $z$, $\zeta$, and $c_{3}$ given in (6.2), (6.4), and (6.6). The derivation of (6.14) is straightforward, but rather complicated. For example, the first step is to write $x$ as a function of $\zeta$ by inverting the relation in (6.4) with $A$, $B$ given in (6.2). This gives

$x$ $=\frac{V+4\zeta\sqrt{W}}{2U},$
$U$ $=(\alpha+\beta+2)^{2}+2\zeta^{2}[3(\alpha+\beta)+8],$
$V$ $=2(\alpha-\beta)[\alpha+\beta+2(1+\zeta^{2})],$
$W$ $=2(\alpha+1)(\beta+1)(\alpha+\beta+4)+4\zeta^{2}[\alpha^{2}+\alpha\beta+\beta^{2}+5(\alpha+\beta)+8].$

With this $x$, the quantities $z$ and $c_{3}$ of (6.4) and (6.6) should be used to construct $F(\zeta)$ and $G(\zeta)$ of (4.11).

Acknowledgment. J. L. López wants to thank C.W.I. of Amsterdam for its scientific support and hospitality during the realization of this work. Work carried out under project MAS2.8 Exploratory research.

References

## References

- [1] R. Askey and M. E. H. Ismail, Recurrence relations, continued fractions, and orthogonal polynomials, Mem. Amer. Math. Soc. 300 (1984), 47–68.
- [2] L. Carlitz, On some polynomials of Tricomi, Boll. Un. Mat. Ital. 13 (1958), 58–64.
- [3] F. Calogero, Asymptotic behaviour of the zeros of the (generalized) Laguerre polynomials $L_{n}^{\alpha}(x)$ as the index $\alpha\to\infty$ and limiting formula relating Laguerre polynomials of large index and large argument to Hermite polynomials, Lettere al Nuovo Cimento 23 (1978), 101–102.
- [4] T. S. Chihara, An Introduction to Orthogonal Polynomials, Gordon and Breach, New York, 1978.
- [5] T. S. Chihara and M. E. H. Ismail, Orthogonal polynomials suggested by a queuing model, Adv. Appl. Math. 3 (1992), 441–462.
- [6] C. L. Frenzen and R. Wong, Uniform asymptotic expansions of Laguerre polynomials, SIAM J. Math. Anal. 19 (1988) 1232–1248.
- [7] W. M. Y. Goh and J. Wimp, On the asymptotics of the Tricomi-Carlitz polynomials and their zero distributions I, SIAM J. Math. Anal. 25 (1997), 420–428.
- [8] , The zero distribution of the Tricomi-Carlitz polynomials, Computers Math. Applic. 33 (1997), 119–127.
- [9] F. W. J. Olver, Asymptotics and Special Functions. Academic Press, New York, 1974. Reprinted in 1997 by A. K. Peters.
- [10] G. Szego, Orthogonal Polynomials, 4th edition, Amer. Math. Soc. Colloq. Publ. 23, Providence, R. I., 1975.
- [11] N. M. Temme, Special Functions: An Introduction to the Classical Functions of Mathematical Physics, Wiley, New York, 1996.
- [12] F. G. Tricomi, Equazioni Differentiali, Torino, 1948; English edition: Differential equations, Blackie and Son, Boston, 1961.
- [13] R. Wong, Asymptotic Approximations of Integrals, Academic Press, New York, 1989.

DEPARTAMENTO DE MATÉMATICA APLICADA, FACULTAD DE CIENCIAS, UNIVERSIDAD DE ZARAGOZA, 50009-ZARAGOZA, SPAIN

E-mail: jllopez@posta.unizar.es

P.O. Box 94079, 1090 GB AMSTERDAM, THE NETHERLANDS

E-mail: nicot@cwi.nl