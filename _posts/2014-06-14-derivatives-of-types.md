---
layout: post
title: On the derivatives of types
---

<center><h1 style="color: red; background-color: yellow;">draft draft draft draft draft</h1></center>

On today's show:

* Table of Contents
{:toc}

We also have an unusually large body of references today. Out of respect for the work done by these authors, we will list our references here, at the top:

* Hasegawa, Ryu. [Two applications of analytic functors](http://www.sciencedirect.com/science/article/pii/S0304397500003492) ([local copy](/assets/type-deriv/Hasegawa.pdf)).
* McBride, Conor.
    * [The Derivative of a Regular Type is its Type of One-Hole Contexts](http://strictlypositive.org/diff.pdf) ([local copy](/assets/type-deriv/diff.pdf)).
    * [Clowns to the left of me, jokers to the right](http://strictlypositive.org/CJ.pdf) ([local copy](/assets/type-deriv/CJ.pdf)).
* Piponi, Dan.
    * [Finite Differences of Types](http://blog.sigfpe.com/2009/09/finite-differences-of-types.html).
    * [Divided Differences and the Tomography of Types](http://blog.sigfpe.com/2010/08/divided-differences-and-tomography-of.html)
* Yorgey, Brent. [Species and functors and types, oh my!](http://dl.acm.org/citation.cfm?id=1863542&picked=formats) ([local copy](/assets/type-deriv/species-pearl.pdf)).

Some other interesting things to consider:

* [Combinatorial species](en.wikipedia.org/wiki/Combinatorial_species).
* [Differential logic](http://intersci.ss.uci.edu/wiki/index.php/Differential_Logic_:_Introduction).
* Again from Dan Piponi, [Using Lawvere theories to combine effects](http://blog.sigfpe.com/2012/02/using-lawvere-theories-to-combine.html).

Introduction
============

Consider the algebraic data type

{% highlight coq %}
Inductive List (X: Type): Type :=
  | nil: List X
  | cons: X -> List X -> List X.
{% endhighlight %}

We can associate a polynomial equation with this definition:
`\[ L(X) = 1 + X \cdot L(X) \]`
which we interpret as follows: a `List(X)` (`\(L(X)\)`) is either `nil` (`\(1\)`) or (`\(+\)`) a pair (`\(\cdot\)`) consisting of an `X` (`\(X\)`) and another `List(X)` (`\(L(X)\)`).

If we interpret `\(L(X)\)` as being an element of the [ring of formal power series](http://en.wikipedia.org/wiki/Formal_power_series) `\(\mathbb C[[X]]\)`, we may use the equation above to get an expression for `\(L(X)\)`:
`\[
\begin{align*}
  L(X) & = 1 + X \cdot L(X) \\
  L(X) - X \cdot L(X) & = 1 \\
  L(X)(1 - X) & = 1 \\
  L(X) & = \frac{1}{1 - X} \mathrm,
\end{align*}
\]`
noting that `\(1 - X\)` is a unit in the ring `\(\mathbb C[[X]]\)` (recall that `\(\sum_{n=0}^\infty a_nX^n\)` is a unit in `\(\mathbb C[[X]]\)` is a unit iff `\(a_0\)` is a unit in `\(\mathbb C\)`, i.e. when `\(a_0 \neq 0\)`).


An algebraic interlude into `\(\mathbb C[[X]]\)`
------------------------------------------------

There is a grading of `\(\mathbb C[[X]]\)` by "least-degree" which can be notationally-handy to use. We define
`\[
\begin{align*}
  \mathbb C[[X]]_n    & = \left\{ a X^n : a \in \mathbb C \right\} \text{ for } 0 \leq n \mathrm, \\
  \mathbb C[[X]]_{n<} & = \bigoplus_{m=n+1}^\infty \mathbb C[[X]]_m \text{ for } -1 \leq n \mathrm,
\end{align*}
\]`
Then for each `\(0 \leq n\)` we have:
`\[ \mathbb C[[X]] = \left( \bigoplus_{m=0}^n \mathbb C[[X]]_m \right) \oplus \mathbb C[[X]]_{n<} \mathrm. \]`

For `\(p(X) = \sum_{n=0}^\infty a_nX^n \in \mathbb C[[X]]\)`, we define the "degree" `\(\deg p(X)\)` of `\(p(X)\)` to be the least `\(k \geq 0\)` such that `\(a_k \neq 0\)`, with `\(\deg 0\)` left undefined. Thus `\(p(X)\)` has degree `\(0\)` if `\(p(X)\)` has a non-zero constant term; it has degree `\(n > 0\)` if it has a zero coefficient for `\(X^m\)` for all `\(m < n\)`, but a non-zero coefficient for `\(X^n\)`.

Viewing `\(\mathbb C[[X]]\)` as a `\(\mathbb C\)`-algebra, there is a [derivation](http://en.wikipedia.org/wiki/Derivation_(differential_algebra)) `\(\partial_X : \mathbb C[[X]] \to \mathbb C[[X]]\)` given by
`\[ \partial_X\left(\sum_{n=0}^\infty a_nX^n\right) = \sum_{n=1}^\infty n a_n X^{n-1} \mathrm, \]`
so that we may regard `\(\mathbb C[[X]]\)` as a [differential algebra](http://en.wikipedia.org/wiki/Differential_algebra).

Of course, one important property of `\(\mathbb C[[X]]\)` is that there is a "composition" operator:
`\[ \circ : \mathbb C[[X]] \times \mathbb C[[X]]_{0<} \to \mathbb C[[X]] \]`
In other words, for `\(g(X), f(X) \in \mathbb C[[X]]\)`, the composition `\(g(f(X)) = g \circ f\)` is defined whenever `\(f\)`'s constant term is `\(0\)`.

The derivation `\(\partial_X\)` is well-behaved with respect to composition, in that we have a "chain rule:"
`\[ \partial_X(g \circ f) = ((\partial_X g) \circ f) \cdot \partial_X f \mathrm. \]`

In short, `\(\partial_X\)` behaves like the derivative with respect to `\(X\)`, according to the rules you know from calculus, as long as you are mindful of when you perform division (you can only divide by elements of degree `\(0\)`) and composition (you can only compute `\(g \circ f\)` if `\(f\)` is of degree `\(1\)` or higher).


Returning to the `List(X)` type
-------------------------------

Let's apply the derivation `\(\partial_X\)` to `\(L(X)\)`. There are two obvious ways to do this, and for fun we'll do them both.

The first way is to apply the operator to both sides of the equation `\(L(X) = 1 + X \cdot L(X)\)` and solve for `\(\partial_X L(X)\)`:
`\[
\begin{align*}
  \partial_X L(X) & = \partial_X(1 + X \cdot L(X)) \\
  \partial_X L(X) & = \partial_X 1 + \partial_X(X \cdot L(X)) \\
  \partial_X L(X) & = \partial_X X \cdot L(X) + X \cdot \partial_X L(X) \\
  \partial_X L(X) & = L(X) + X \cdot \partial_X L(X) \\
  \partial_X L(X) - X \cdot \partial_X L(X) & = L(X) \\
  \partial_X L(X) \cdot (1 - X) & = L(X) \\
  \partial_X L(X) & = \frac{L(X)}{1 - X} \\
  \partial_X L(X) & = (L(X))^2 \mathrm.
\end{align*}
\]`

The second way is to apply the operator to the equation `\(L(X) = 1/(1-X)\)`:
`\[
\begin{align*}
  \partial_X L(X) & = \partial_X \left( (1-X)^{-1} \right) \\
                  & = \left(\partial_X (X^{-1}) \circ (1-X)\right) \cdot \partial_X(1-X) \\
                  & = \left((-X^{-2}) \circ (1-X) \right) \cdot (-1) \\
                  & = (-(1-X)^{-2}) (-1) \\
                  & = (1-X)^{-2} \\
                  & = (L(X))^2 \mathrm.
\end{align*}
\]`
This calculation is a bit fishy, owing to the part where we write `\(X^{-1}\)`. After all, `\(X\)` is not a unit in `\(\mathbb C[[X]]\)`, so such a term seems like nonsense. We also have the expression `\(1-X\)` on the right-hand side of the `\(\circ\)` operator, which also doesn't seem right, as `\(1 - X \not\in \mathbb C[[X]]_{0<}\)`. Regardless, we arrived at the same answer as with our other method.

One may think it odd that the "derivative" of the `List(X)` type should be a pair of lists `List(X)` `\(\cdot\)` `List(X)`, but this is precisely the interpretation of the equation `\(\partial_X L(X) = (L(X))^2\)`. There is a combinatorial interpretation of this phenomenon. In short, if `\(L(X)\)` represents a `List(X)`, then `\(\partial_X L(X)\)` represents a "`List(X)` with an `X`-shaped hole in it." Now things become a bit more clear: after all, if you have a list, say
<center>`[ a ; b ; c ; d ]`,</center>
and you remove an element (say `b`), you're left with two lists with a hole in between, as in
<center>`([ a ], [ c ; d ])`.</center>

This sort of trick works with all sorts of container types. For instance, we might model a `\(k\)`-fold tree with the equation
`\[ T_k(X) = 1 + X \cdot (T_k(X))^k \mathrm. \]`
Of course we know `\(T_1(X) = L(X)\)`.

For `\(1 \leq k\)`, we can compute `\(\partial_X T_k(X)\)`, applying the same method as our first technique for computing `\(\partial_X L(X)\)`:
`\[
\begin{align*}
  \partial_X T_k(X) & = \partial_X \left( 1 + X \cdot (T_k(X))^k \right) \\
  \partial_X T_k(X) & = \partial_X 1 + \partial_X \left( X \cdot (T_k(X))^k \right) \\
  \partial_X T_k(X) & = (\partial_X X)(T_k(X))^k + X\left(\partial_X (T_k(X))^k\right) \\
  \partial_X T_k(X) & = (T_k(X))^k + X \cdot \left( k (T_k(X))^{k-1} \cdot (\partial_X T_k(X)) \right) \\
  \partial_X T_k(X) & = (T_k(X))^k + kX \cdot (T_k(X))^{k-1} \cdot (\partial_X T_k(X)) \\
  \partial_X T_k(X) - kX \cdot (T_k(X))^{k-1} \cdot (\partial_X T_k(X)) & = (T_k(X))^k \\
  \partial_X T_k(X) \cdot (1 - kX \cdot (T_k(X))^{k-1}) & = (T_k(X))^k \\
  \partial_X T_k(X) & = \frac{(T_k(X))^k}{1 - kX \cdot (T_k(X))^{k-1}} \\
  \partial_X T_k(X) & = (T_k(X))^k \cdot L\left(kX \cdot (T_k(X))^{k-1}\right) \mathrm.
\end{align*}
\]`

Once more, the combinatorial interpretation is direct: the "derivative" of the `\(k\)`-fold tree type of `X`'s is a "`\(k\)`-fold tree of `X`'s with an `X`-shaped hole in it." How does that relate to the expression we computed above? Imagine you've been handed a tree and you select a node in the tree in-which to poke a hole. How does the type corresponding to `\(\partial_X T_k(X)\)` describe the resulting tree-with-hole? It's surprisingly simple:

* The branch factor `\((T_k(X))^k\)` represents the branches eminating from the node where you poked the hole.
* The list factor `\(L\left(kX \cdot (T_k(X))^{k-1}\right)\)` represents a trace from the node with the hole back to the root of the tree. Each element of the list corresponds to one upward-step towards the root. The data within that element indicates which of that node's branches you are coming from (the `\(k\)` factor), the data held at that node (the `\(X\)` factor), and the `\(k-1\)` branches you *aren't* coming from (the `\((T_k(X))^{k-1}\)` factor). The case where the hole was poked in the root of the tree is represented by the special case where the data held in the list factor is simply the empty list.


Pausing to consider the meaning of our arithmetic
-------------------------------------------------

Now let us work in the ring `\(\mathbb C[[m, f]]\)`, and consider the system of equations
`\[
\begin{align*}
  M(f, m) & = m + F(f, m) \mathrm, \\
  F(f, m) & = f + M(f, m) \cdot F(f, m) \mathrm.
\end{align*}
\]`
This system is based on a familiar combinatorial description of the Fibonacci numbers. It goes something like this: you are looking at a colony of bees. Unfertilized females lay eggs which hatch as males, while fertilized females lay eggs which hatch as females.

In these equations, we suppose there is a set of original males (described by the type `\(m\)`) as well as a set of original females (described by the type `\(f\)`). Then `\(M(f,m)\)` says that a male is either one of the original males (`\(m\)`), or is the son of a female (`\(F(f,m)\)`). Similarly, `\(F(f,m)\)` says that a female is either one of the original females (`\(f\)`), or is the daughter of a male and a female (`\(M(f, m) \cdot F(f, m)\)`).

By applying the same methods as before, may solve for `\(F(f, m)\)` quite easily, yielding `\(F(f, m) = f \cdot L(M(f, m))\)`, so that
  `\[ M(f, m) = m + f \cdot L(M(f, m)) \mathrm. \]`

Let us now pause to consider the meaning of this expression, given our original description of the mating bees. A male bee is either one of the original male bees (`\(m\)`), or it is the son of a female bee. So how does `\(f \cdot L(M(f, m))\)` describe the mother of a male bee?

If you are into functional programming, you may recognize that the answer is given by a fold. Let's define some operators:
`\[
\begin{align*}
  \downarrow & : F(f, m) \to M(f, m) \mathrm, \\
  \downdownarrows & : M(f, m) \times F(f, m) \to F(f, m) \mathrm.
\end{align*}
\]`

Then we may write a function:

<code>
Inductive M' \(f\) \(m\) : Type :=<br>
  | InL : \(m\) -> M' \(f\) \(m\)<br>
  | InR : \(f\) -> List (M' \(f\) \(m\)) -> M' \(f\) \(m\).<br>
<br>
male : M' \(f\) \(m\) -> \(M(f, m)\)<br>
male(InL m) = m<br>
male(InR f []) = \(\downarrow\) f<br>
male(InR f m::ms) = male (InR (male m \(\downdownarrows\) f) ms).
</code>

Or, if you prefer, we may write it as a fold:

<code>
male : M' \(f\) \(m\) -> \(M(f, m)\)<br>
male(InL m) = m<br>
male(InR f ms) = \(\downarrow\) (fold (fun f' m => male m \(\downdownarrows\) f') f ms).
</code>

The presence of the `fold` operation is caused by the fixed-point in our original definition equations for `\(M\)` and `\(F\)`.

The structure of the `male` function follows directly from our algebraic operations:

* Our original defining equation `\(M(f, m) = m + F(f, m)\)` suggests the function<br>
<code>
male : \(m + F(f, m)\) -> \(M(f,m)\)<br>
male (InL m) = m<br>
male (InR f) = \(\downarrow\) f.
</code>

* The equation `\(F(f, m) = f \cdot L(M(f, m))\)` suggests the function<br>
<code>
female : \(f \cdot L(M(f, m))\) -> \(F(f, m)\)<br>
female (f, ms) = foldr (fun m f' => m \(\downdownarrows\) f') f ms.
</code>

The process of substituting our expression for `\(F(f, m)\)` into our expression for `\(M(f, m)\)` corresponds to a change both in the type signature of `male` (as expected) as well as a change of its structure in the effected branch.

The most interesting part is to go back to where the `fold` was introduced. This occured back when we solved for `\(F(f, m)\)`. Our original equation `\(F(f, m) = f + M(f, m) \cdot F(f, m)\)` suggests the function

<code>
female : \(f + M(f, m) \cdot F(f, m)\) -> \(F(f ,m)\)<br>
female (InL f) = f<br>
female (InR m f) = m \(\downdownarrows\) f.
</code>

So something about solving for `\(F(f,m)\)` introduced a `fold` into our function. Very interesting.

Let's look at a simpler example of this behavior. Recall that `\(L(X) = 1 + X \cdot L(X)\)`. Consider the operator
`\[ \operatorname{cons} : X \times L(X) \to L(X) \mathrm. \]`
This suggests a function

<code>
list : \(1 + X \cdot L(X)\) -> \(L(X)\)<br>
list (InL 1) = 1<br>
list (InR x xs) = \(\operatorname{cons}\) x xs.
</code>

We then perform the following algebraic operations on `\(L(X) = 1 + X \cdot L(X)\)`, mirroring the steps we used to solve for `\(F(f, m)\)`:
<center><table width="100%"><tr>
<td>\[
\begin{align*}
  L(X) & = 1 + X \cdot L(X) \\
  L(X) - X \cdot L(X) & = 1 \\
  L(X) (1 - X) & = 1 \\
  L(X) & = \frac{1}{1 - X} \\
  L(X) & = L(X)
\end{align*}
\]</td>
<td>\[
\begin{align*}
  F(f,m) & = f + M(f,m) \cdot F(f,m) \\
  F(f,m) - M(f,m) \cdot F(f,m) & = f \\
  F(f,m)(1 - M(f,m)) & = f \\
  F(f,m) & = \frac{f}{1 - M(f,m)} \\
  F(f,m) & = f \cdot L(M(f,m))
\end{align*}
\]</td>
</tr></table></center>

So by comparison, if the operations on `\(F(f,m)\)` suggest a function like

<code>
female : \(f \cdot L(M(f, m))\) -> \(F(f, m)\)<br>
female (f, ms) = foldr (fun m f' => m \(\downdownarrows\) f') f ms.
</code>

then we should expect the operations on `\(L(X)\)` to yield a function like

<code>
list : \(L(X)\) -> \(L(X)\)<br>
list xs = foldr (fun x xs' => cons x xs') nil xs
</code>

which is interesting, seeing as this is the identity function on `\(L(X)\)`.


What is going on?
-----------------

A few things have been observed:

* Recursive type definitions can be interpreted as equations in `\(\mathbb C[[X]]\)`.
* The derivation `\(\partial_X\)` of a recursive type is a new recursive type, representing data from the original type "with a hole in it."
* The algebraic manipulaiton of these type definitions suggests similar manipulation of functions defined on these types, though the apparent introduction of `foldr` remains mysterious.

This is the story so-far, as we've told it. We now come to the question: how do we interpret this peculiar blend of recursive data types and "calculus" in `\(\mathbb C[[X]]\)`?

One answer is by way of *combinatorial species*. A "species" is an endo-functor on the category of finite sets and bijections. The idea is that the image under a species should be thought-of as describing the various ways in which these structures may be placed on an element of the domain, e.g. by yielding the permutation group of a given set, or by yielding the set of all finite-depth binary trees whose nodes are marked by members of a given set, etc.

For any species `\(\mathsf F\)`, we know that for any finite set `\(A\)`, the number of elements in the set `\(\mathsf F(A)\)` depends only on the number of elements in `\(A\)`. (This is a simple consequence of the fact that `\(\mathsf F\)` acts functorially, and the basic fact that two finite sets have the same number of elements if and only if a bijection exists between them.)

Thus, for any species `\(\mathsf F\)`, we may define a sequence `\(\big(F_n\big)_{n=0}^\infty\)` by
`\[ F_n = \#\mathsf F(A) \text{ for any } A \text{ with } \#A = n \mathrm. \]`
From this we may define the "exponential generating function" of `\(\mathsf F\)`:
`\[ F(x) = \sum_{n=0}^\infty \frac{F_n}{n!} x^n \]`
which we recognize as an element of `\(\mathbb C[[x]]\)`.

Here is an important example. Let `\(\mathsf S\)` be the species of permutations, which takes a finite set `\(A\)` to the permutation group `\(S_A\)`. As is well known, `\(\# S_A = (\# A)!\)`, so that `\(S_n = n!\)`. Then
`\[ S(x) = \sum_{n=0}^\infty \frac{n!}{n!} x^n = \sum_{n=0}^\infty x^n \mathrm. \]`
This is, notably, the Taylor series of the function `\(L(x) = \frac{1}{1-x}\)`. In other words, *the generating function for the species of permutations has the Taylor series of the list type*.

Permutations and lists are not the same thing. For instance, the set `\(S_A\)` of permutations of `\(A\)` is finite, while the set of finite lists whose elements are drawn from `\(A\)` is (when `\(A\)` is non-empty) countably-infinite. Yet they both have this mysterious `\(\frac{1}{1-x}\)` in common. What are we to make of that?

Here is another example. Let `\(\mathsf U\)` be the species of 2-tuples, which takes a finite set `\(A\)` to the finite set `\(A^2\)`. Of course, `\(\# (A^2) = (\# A)^2\)`, so that `\(U_n = n^2\)`, and
`\[ U(x) = \sum_{n=0}^\infty \frac{n^2}{n!} x^n \mathrm, \]`
which is the Taylor series of the function `\(x \mapsto x(x + 1)e^x\)`, which does not have an obvious interpretation as a type. (If we were to write the 2-tuple type as an equation in `\(\mathbb C[[X]]\)`, we'd cook up something rather bland: `\(U(X) = X^2\)`.)

Today we are going to try to piece all of this together.


Analytic functors
=================

First, forget about all of the notation and definitions given so-far, so that we may start with a clean-slate in unraveling all of this.

Now we define some important categories:

* Let `\(\mathbf{Set}\)` be the category of sets and functions between them. We let `\([n]\)` denote the isomorphism class of finite sets with `\(n\)` elements.


A functor `\(\mathsf F : \mathbf{Set} \to \mathbf{Set}\)` is said to be "analytic" if it is naturally-isomorphic to a functor of the form
  `\[ \sum_{i \in I} \operatorname{Hom}_{\mathbf{Set}}(X_i, -)/G_i \mathrm, \]`
with:

* each `\(X_i\)` is a finite set;
* each `\(G_i\)` is a subgroup of the automorphism group `\(\operatorname{Aut}_{\mathbf{Set}}(X_i)\)` (i.e. the permutation group `\(S_{X_i}\)`);
* and where, for each `\(X\)`, we understand `\(\operatorname{Hom}_{\mathbf{Set}}(X_i, X)/G_i\)` to be the orbit space of the action of `\(G_i\)` on `\(\operatorname{Hom}_{\mathbf{Set}}(X_i, X)\)` given by
  `\[ p \cdot f = f \circ p^{-1} \mathrm. \]`


Examples and important classes
------------------------------

A basic example is the functor `\(\mathsf{exp} : \mathbf{Set} \to \mathbf{Set}\)`, given by
  `\[ \mathsf{exp} = 1 + X/S_{[1]} + X^2/S_{[2]} + X^3/S_{[3]} + \cdots \mathrm. \]`
Here `\(X^n\)` is the functor which maps a set to its `\(n\)`th cartesian power, which as a functor is represented by `\([n]\)`, "the" set of `\(n\)` elements (that is, the functor `\(X^n\)` is naturally-isomorphic to the functor `\(\operatorname{Hom}_{\mathbf{Set}}([n], -)\)`). Of course, `\(S_{[n]}\)` is the familiar group of permutations on `\([n]\)`, which has cardinality `\(n!\)`, so that this functor resembles the Taylor series of the function `\(x \mapsto e^x\)`.

It is easy to ascribe combinatorial meaning to the terms in this series. Specifically, given a set `\(B\)`, an element of the set `\(B^n/S_{[n]}\)` is an orbit of an `\(n\)`-tuple of elements of `\(B\)` under the shuffling action of the permutation group `\(S_{[n]}\)`. In other words, it's a tuple without ordering; thus, `\(B^n/S_{[n]}\)` consists of multi-sets of cardinality `\(n\)` with elements drawn from `\(B\)`. So the functor `\(\mathsf{exp}\)` maps a set `\(B\)` to the family of finite multi-sets of elements of `\(B\)`. Alternatively, `\(\mathsf{exp}\)` is the monad formed by the composition of the free commutative monoid functor with the monoid-forgetful functor.

An analytic functor is said to be "exponential" if the groups `\(G_i\)` are chosen to be all of `\(\operatorname{Aut}_{X_i}\)`. It is said to be "normal" if the `\(G_i\)` are all chosen to be the trivial group (i.e., the group with one element, which acts on `\(X_i\)` by identity).

As we've seen, the functor `\(\mathsf{exp}\)` is an exponential functor. Let's look at some normal functors:

* The list functor `\(\mathsf{List} = 1 + X + X^2 + X^3 + \cdots\)`, which we recognize (as combinatorialists) as the functor which maps a set to the family of all finite (ordered) lists of elements of that set. Alternatively, this functor is the monad realized by the composition of the free-monoid functor with the monoid-forgetful functor.
* The binary-tree functor `\(\mathsf{BinTr} = \sum_{n=1}^\infty \frac{1}{n} \binom{2n-2}{n-1} X^n\)`, which we recognize (as combinatorialists) as the functor which maps a set to the family of all finite (ordered) binary trees whose leaves carry elements of that set. Of course we recognize `\(\frac{1}{n} \binom{2n-2}{n-1}\)` as the `\(n\)`th Catalan number. Alternatively, this functor is the monad realized by the composition of the free magma functor with the magma-forgetful functor.

From these examples, we may begin to form some intuition: exponential functors yield structures which are unordered/commutative (such as multisets), while normal functors yield structures which are ordered/non-commutative (such as lists).


Composition of analytic functors
--------------------------------

From the outset, it's not clear that the composition of two analytic functors will again be analytic. Fortunately this does turn out to be the case (Corollary 1.18 in Hasegawa). Let `\(\mathsf G = \sum_{i\in I} \operatorname{Hom}_{\mathbf{Set}}(X_i, -)/G_i\)` and `\(\mathsf H = \sum_{j\in J} \operatorname{Hom}_{\mathbf{Set}}(Y_i, -)/H_i\)`. Then the composition `\(\mathsf H \circ \mathsf G\)` is again analytic, with
`\[ \mathsf H \circ \mathsf G \cong \sum_{[e] \in H(I)} \operatorname{Hom}_{\mathbf{Set}}\left( \sum_{y \in Y_j} X_{e(y)} , -\right)/K_e \mathrm, \]`
where, for each `\(e \in \operatorname{Hom}_{\mathbf{Set}}(Y_j, I)\)`, we let `\([e]\)` the orbit of `\(e\)` under the action of `\(H_j\)`, and where (for a given representative `\(e\)` of the coset `\([e]\)`) we let
`\[ K_e = \prod_{i \in I} G_i \operatorname{Wr}(H_j)^{e^{-1}(i)}_{e^{-1}(i)} \mathrm, \]`
that is, a catesian product of wreath products, where the `\(i\)`th wreath product acts on `\(X_i \times e^{-1}(i)\)`.





