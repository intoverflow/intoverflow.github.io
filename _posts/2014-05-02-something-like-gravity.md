---
layout: post
title: Something like gravity
---

<center><h1 style="color: red; background-color: yellow;">draft draft draft draft draft</h1></center>

<center><i>This draft is loaded with errors and omissions. There are a lot of things I had planned to say about this model - particularly about the ways in which it is non-physical - but which I never had a chance to write down. Some of the analysis is also flawed. I'm leaving it here as a reminder to myself of the direction I was going. Ye have been warned.</i></center>


Introduction
============

A long time ago, Einstein considered the following question: what would an EM field look-like as measured in a frame which was moving at the speed of light? In a classical world, one would expect the field to look constant in time, periodic in space - exactly what one sees if they fly over the ocean at the same speed and direction of an oceanic wave below.

But Maxwell's equations don't admit such solutions. Contrary to this, Maxwell's equations [predict that the speed of light is constant](http://en.wikipedia.org/w/index.php?title=Maxwell%27s_equations&oldid=606783493#Vacuum_equations.2C_electromagnetic_waves_and_speed_of_light) in all frames, which means the field could not be sitting still - it would still be moving at `\(c\)`!

This question ultimately led to the development of special relativity in 1905, a theory which replaced the usual Galileo-Newton `\(\mathbb R^3\)` geometry of space (where `\(ds^2 = dx^2 + dy^2 + dz^2\)`) with the Minkowski `\(\mathbb R^4\)` geometry of spacetime (where `\(ds^2 = -c^2dt^2 + dx^2 + dy^2 + dz^2\)`).

To fancy things up a bit, 10 years later he published his theory of general relativity, which described properly the geometry of spacetime. The theory takes the Minkowski spacetime of special relativity as a local model for a manifold whose curvature is interpreted as gravity. It's a lovely bit of mathematical physics and learning about it has made my life better.

General relativity has many interesting features:

* It says that the phenomena of gravity is not a fundamental force, but rather occurs as an artifact (if you will) of the curvature of spacetime.
* It says that the curvature of space time evolves according to the presense of mass and energy (including, interestingly, the energy expressed by the curvature itself, in the form of gravitational potential).
* It says that changes in curvature radiate at the speed of light, meaning that the gravitational attraction between two bodies is not instantaneous action-at-a-distance.

Computantionally, all of this sounds like good news at first. Einstein gave us equations which we can use, in principle, to calculate everything we need. Since GR is a *local* theory, the problem should submit to grid computing rather nicely (the local-action property implying that our simulation should have good data locality).

Despite all of this, however, GR is notoriously difficult to simulate. There are at-least two major problems.

The first is that GR simulations tend to encounter both very tiny and very large numbers. Unfortunately, floating point units tend to merely support numbers which are somewhat-tiny to somewhat-large. Thus one must take great care to avoid underflow and overflow.

The second is related to how our coordinates evolve. Remember that GR says that the curvature of spacetime evolves; thus, our coordinates evolve as well. Unfortunately, they may evolve to possess singularities. We can change coordinates, but our transition maps must also be non-singular. Care must be taken to avoid these singularities, as they will wreck our numerical stability.

There are reasons why these problems are hard to avoid: we do not have decision procedures which can detect well in advance whether or not a simulation will encounter these problems. Thus, the simulation must be able to adapt to these danges as they develop.

And so I ask the question: how would one design a theory of gravity which was qualitatively similar to GR, but easy to simulate computationally? This is a silly hypothetical; if we do not require *quantitative* similarity, the theory will lack physical meaning. Still, as design questions go it's a fairly unique one, so let's explore it a bit.


Non-local gravity
=================

Newton's theory of gravity seems like a good place to start. Newtonian gravity describes an attractive force between two bodies. Supposing these bodies are distance `\(r\)` apart, and that they have masses `\(m_1, m_2\)` respectively, then the force `\(F\)` satisfies

`\[ F \propto \frac{m_1 m_2}{r^2} \mathrm. \]`

Let's just say they're equal.

Now suppose we have a body `\(B\)` with mass `\(M\)`. Define a field `\(G(\vec x) = - \frac{M}{\|\vec x\|^3} \vec x\)`. Then if we have a body `\(C\)` with mass `\(m\)` at displacement `\(\vec x\)` from `\(B\)`, the attractive force acting on `\(C\)` will be equal to `\(mG(\vec x)\)`.

More generally, let's fix a coordinate frame, suppose we have bodies `\(B_1,...,B_k\)` with masses `\(m_1,...,m_k\)` at locations `\(\vec p_1,...,\vec p_k\)`. Define

`\[ G(\vec x) = \sum_{i=1}^k \frac{m_i}{\|\vec x - \vec p\|^3}(\vec x - \vec p) \mathrm. \]`

Then a body with mass `\(n\)` at position `\(\vec q\)` will experience a gravitational force of `\(nG(\vec q)\)`.

This is lovely and all, but for large `\(k\)`, computation of `\(G\)` becomes troublesome. The problem is that, in order to evaluate `\(G(\vec x)\)`, we must cycle through each of our bodies. In a grid compute scenario, this is sure to have poor data locality.

The `\(G\)` field is nice because it gives us a simple tool for computing the gravitational force on a given body. It would be nice to have something like that, but which only considered *local* action.


Local gravity
=============

Let's simplify things a bit. First, let's work in 2 dimensions, not 3. Second, let's discretize space by a regular tiling, say by triangles. We will define a vector field `\(W\)` similar to `\(G\)` over our triangles.

However, unlike our action-at-a-distance definition of `\(G\)`, we are going to model our field using only local interactions, evolving in time. At each time step, the vector in any given triangle will be re-computed as a weighted average of the neighboring vectors (using the values from the previous time step). When a triangle contains matter, its contributions to its neighbors will be boosted in some way to take the mass into account.

Okay, time to form our tiling of the plane by triangles. We will use the tiling generated by the equilateral triangle with vertices at

`\[ (0, 1), (-\sqrt{3}/2,-1/2), (\sqrt{3}/2,-1/2) \mathrm. \]`

Note that with this tiling, some triangles point up (such as the one whose vertices we just gave) while others point down (such as each of his 3 nearest neighbors).

When we are stepping a given triangle, we will change coordinates to place the center of that triangle at the origin. It will sample its 12 nearest neighbors (3 at distance 1, 6 at distance `\(\sqrt{3}\)`, and 3 at distance 2), and take on a weighted average, adjusted for the radial-decay of gravitational energy.

This situation may be depicted quite readily in Sage (see the last section for code). There are two pictures to consider, depending on whether we are focusing on an "up" triangle or a "down" triangle:

<img src="/assets/grav_up.png" width="50%"> <img src="/assets/grav_down.png" width="50%">

Within each triangle, we have written the coordinates of the center of the triangle and the distance from this point to the origin. We will store the `\(W\)` vector field in a two-dimensional array; the triangles have been labeled with their indices into this array, relative to the origin. (The indices discrete into `\(W\)` are in one-to-one correspondence with the coordinates of the centers of triangles in our tiling; notationally, given indices `\(i,j\)`, the coordinates of the center of the corresponding triangle will be denoted `\(\Delta(i,j)\)`. An explicit form for `\(\Delta(i,j)\)` appears in our Sage code. Note that the equation depends on whether or not `\(i,j\)` is an up or down triangle, as well as whether or not the origin (in your coordinate frame) is up or down.)

The value of the `\(W\)` field at step `\(t\)` will be denoted `\(W_t\)`. To run our simulation, we need to cook up a stepping relation of the form

`\[ W_{t+1}(x,y) = \sum_{\substack{s \in \{1,\sqrt{3},2\} \\ \| \Delta(i,j) - \Delta(x,y) \| = s}} \alpha_s(W_t(i,j)) \mathrm, \]`

that is, a way to express `\(W_{t+1}(x,y)\)` as a weighted sum of near-by points at the previous time step. Here the functions `\(\alpha_s\)` are used to weigh the terms according to their associated distance from the point of interest `\((x,y)\)`. By keeping `\(\frac{\alpha_s(w)}{w} < 1\)`, we ensure there is some kind of decay in magnitude as field data travels through space.

We'd like this decay to follow an inverse-square law, much like our field `\(G\)` above. We can look to our `\(G\)` field for guidance.

For a moment, let's restrict to the 1-dimensional case, and let

`\[ \tilde G(r) = -\frac{M}{r^2} \mathrm, \]`

noting the similarity to `\(G\)` (the exponent in the denominator changes from 3 to 2 because, in the case of `\(G\)`, the extra factor is used to normalize the direction vector `\(\vec x\)`, which we need not do in the 1-dimensional case).

Now, letting `\(M=1\)` and taking `\(dr\)` a small change in `\(r\)`, we know

`\[ \begin{align}
  \tilde G(r + dr) & \approx \tilde G(r) + \left.\frac{d \tilde G}{dr}\right|_r dr \\
    & = \tilde G(r) + \frac{2M}{r^3}dr \\
    & = \tilde G(r) + \frac{2 (- \tilde G(r))}{r} dr \\
    & = \tilde G(r) + \frac{2 (- \tilde G(r))}{\sqrt{M}(- \tilde G(r))^{-1/2}} dr \\
    & = \tilde G(r) + \frac{2 (- \tilde G(r))^{3/2}}{\sqrt{M}} dr \\
    & = \tilde G(r) + 2( -\tilde G(r))^{3/2} dr \mathrm.
\end{align} \]`

An important feature of this expression is that, except when `\(\tilde G(r)=0\)`, we have `\(G(r) < 0 < 2( -\tilde G(r))^{3/2} dr < |G(r)|\)`. All of this suggests that we take

`\[ \begin{align}
  \alpha_s(\vec w) & = \left( \| \vec w \| - 2 \| \vec w \|^{3/2} s \right) \frac{\vec w}{\| \vec w \|} \\
    & = \left(1 - 2\| \vec w \|^{1/2} s\right) \vec w \mathrm.
\end{align} \]`

This isn't a derived equation; it was constructed, using the intuition and form from our analysis of `\(\tilde G(r+dr)\)`. Note that we had to adjust the signs a bit ("`\(-2\)`") to account for the fact that we are scaling the `\(\vec w\)` vector, while in our analysis above we were technically scaling the `\(\mathbf 1\)` "vector". (If it still seems unmotivated, it may be instructive to repeat the `\(\tilde G(r+dr)\)` analysis, but written in terms of the "vector" `\(\tilde G(r) / \|\tilde G(r)\|\)`).

Does this definition behave as we'd like? This depends on `\(s\)`. Our coordinates have us working with values `\(s \in \{1, \sqrt{3}, 2\}\)`. Since we'd like `\(2\|\vec w\|^{1/2}s < 1\)`, we obtain three constraints on our field (corresponding to our three `\(s\)` values). The tightest of these constraints occurs when `\(s=2\)`:

`\[ \|\vec w\| < \frac{1}{16} \]`

What happens if our field violates this constraint? Tracing our reasoning, the result would be a vector which grows in magnitude as it propagates. This phenomena arises as a result of how we discretized space: if we had used smaller triangles, the phenomena would be less pronounced, and in the limit `\(s \to 0\)` we might expect this phenomena not to occur at all.

But we do not have the luxury of working with infinitesimal triangles. For now we'll ignore the problem; perhaps later we will witness some amusing train wrecks because of it.

Well, now we have our `\(\alpha_s\)` functions, and our coordinate charts. Let's get on to simulating it.


Local gravity simulation
========================

Our simulation will consist of three arrays:

* A buffer for `\(W_t\)`
* A buffer for `\(W_{t-1}\)`
* A buffer `\(M_t\)` tracking the mass within each triangle

Our arrays will be finite in dimension, meaning we need to deal with triangles at the boundary in some way. The simplest thing to do would be to set `\(W_t(i,j)=\vec 0\)` when `\((i,j)\)` is located on the boundary.

This is a bit unsatisfactory because of how this affects the neighboring interior triangles. When those triangles are stepped, they will always get the `\(\vec 0\)` vector from their neighbors on the boundary. Why does this matter per-se? When we step the `\(W\)` field, each triangle dissipates its vector to its neighbors; on the following step, each triangle samples its neighbor. During the sampling phase, part of the value obtained is the result of the dissipation. But triangles neighboring the boundary don't get this full effect, because some of their neighbors are constant `\(\vec 0\)`.





Sage code for the triangle diagrams
===================================


{% highlight python %}
# Tested Sage Cloud 2014-12-23
dx = sqrt(3)/2
dy = 1/2
def tri_gen(i, j, fl_a, fl_b):
    aff_a = {-1: 1, 1: 0}[fl_a]
    aff_b = {-1: -1, 1: 0}[fl_b]
    orig = vector((i*dx, (3*j+aff_a+aff_b)*dy))
    a = orig + vector((0, fl_a * 2*dy))
    b = orig + vector((-dx, fl_a * -dy))
    c = orig + vector((dx, fl_a * -dy))
    tri = polygon([a, b, c], fill=False)
    t = text(str(orig) + "\n" + str(orig.norm().n(prec=11)) + "\nW" + str((i,j)), orig, fontsize=5)
    return tri + t

# We have two types of triangles: those pointing up and
# those pointing down. The way we draw them depends on the
# type of triange at the origin. If the origin is up,
# then use the _as_up functions. If the origin is down,
# use the _as_down functions.
def tri_up_as_up((i, j)):
    return tri_gen(i, j, 1, 1)
def tri_down_as_up((i, j)):
    return tri_gen(i, j, -1, 1)
def tri_up_as_down((i, j)):
    return tri_gen(i, j, 1, -1)
def tri_down_as_down((i, j)):
    return tri_gen(i, j, -1, -1)

# An "up" origin:
# radius 0
diagram = tri_up_as_up((0, 0))
# radius 1
for pt in [(-1, 0), (1, 0),  (0, -1)]:
    diagram += tri_down_as_up(pt)
# radius sqrt(3)
for pt in [(-1, 1), (1, 1), (-2, 0), (2, 0), (-1, -1), (1, -1)]:
    diagram += tri_up_as_up(pt)
# radius 2
for pt in [(0, 1), (-2, -1), (2, -1)]:
    diagram += tri_down_as_up(pt)
show (diagram, axes=False)

# A "down" origin:
# radius 0
diagram = tri_down_as_down((0, 0))
# radius 1
for pt in [(-1, 0), (1, 0),  (0, 1)]:
    diagram += tri_up_as_down(pt)
# radius sqrt(3)
for pt in [(-1, -1), (1, -1), (-2, 0), (2, 0), (-1, 1), (1, 1)]:
    diagram += tri_down_as_down(pt)
# radius 2
for pt in [(0, -1), (-2, 1), (2, 1)]:
    diagram += tri_up_as_down(pt)
show (diagram, axes=False)
{% endhighlight %}
