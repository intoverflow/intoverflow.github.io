---
layout: post
title: Finite difference time domain (FDTD) methods
---

Introduction
============

In the design of microwave circuits, one must deal with the fact that the trace geometry has features on the scale of the signal's wavelength, which leads to all sorts of interesting phenomena not typically noticed at lower speeds. This can be a source of headaches, for instance when routing traces, but it can also be a source of opportunity: one can exploit these properties to design "planar" alternatives to lumped components (such as inductors and capacitors). These alternatives are implemented by etching carefully-designed geometries into the board, same as one would for traces and other features.

I became interested in the design of these components. It seems to be a bit of a dark art, with simulators doing the heavy lifting. Ok, how does one simulate such circuits?

[Finite difference time domain](http://en.wikipedia.org/wiki/Finite-difference_time-domain_method) (FDTD) methods provide one solution. In this post, we'll begin to explore these methods.


Background
==========

I began by picking up a copy of [Computational Electrodynamics: The Finite-Difference Time-Domain Method](http://www.seattletechnicalbooks.com/book/9781580538329) by Allen Taflove and Susan C. Hagness. As always I bought it from [Ada's](http://www.seattletechnicalbooks.com/), my local technical book seller. It's a fascinating read describing several optimizations and applications. We'll be following the path set by this book.


The electrodynamics
-------------------

First we must lay out some assumptions. Namely, we'll assume that the materials in our simulation are "linear, isotropic, (and) nondispersive," and we'll allow them to "attenuate `\(\mathrm E\)`- and `\(\mathrm H\)`-fields via conversion to heat energy."

The behavior of EM fields is modeled by Maxwell's equations:

`\[ \begin{aligned}
  \frac{\partial \mathbf B}{\partial t} & = - \nabla \times \mathbf E - \mathbf M \\
  \frac{\partial \mathbf D}{\partial t} & = \nabla \times \mathbf H - \mathbf J \\
  \nabla \cdot \mathbf D & = 0 \\
  \nabla \cdot \mathbf B & = 0
\end{aligned} \]`

where

* `\(\mathbf E\)` is the electric field (volts/meter)
* `\(\mathbf H\)` is the magnetic field (amperes/meter)
* `\(\mathbf D\)` is the electric flux density (coulombs/meter<sup>2</sup>)
* `\(\mathbf B\)` is the magnetic flux density (webers/meter<sup>2</sup>)
* `\(\mathbf J = \mathbf{\hat J} + \sigma \mathbf E\)` is the electric current density (amperes/meter<sup>2</sup>), `\(\mathbf{\hat J}\)` acts as an independent source of `\(\mathbf E\)`-field energy, and `\(\sigma\)` is the electric conductivity (siemens/meter) of the underlying medium
* `\(\mathbf M = \mathbf{\hat M} + \sigma^* \mathbf H\)` is the equivalent magnetic current density (volts/meter<sup>2</sup>), `\(\mathbf{\hat M}\)` acts as an independent source of `\(\mathbf H\)`-field energy, and `\(\sigma^*\)` is the equivalent magnetic loss (ohms/meter) of the underlying medium.

The first two, the laws of Faraday and Ampere, describe the time evolution (on the left-hand side) in terms of the spatial evolution (on the right-hand side). The second two, both named for Gauss, name important physical constraints which are true of real EM fields. According to the [Wikipedia](http://en.wikipedia.org/w/index.php?title=Maxwell%27s_equations&oldid=593989245#Solutions), Gauss' laws follow from Faraday's and Ampere's laws, provided the initial conditions satisfy Gauss' laws. Thus, for the purposes of simulation, one needs only the Faraday and Ampere laws.

So we will henceforth be concerned only with those first two equations.

Now, as stated above, these equations involve 6 fields (`\(\mathbf E\)`, `\(\mathbf H\)`, `\(\mathbf D\)`, `\(\mathbf B\)`, along with our source fields `\(\mathbf{\hat J}\)` and `\(\mathbf{\hat M}\)`). The assumptions we've made about our materials, however, allows us to simplify matters. Namely, we have

`\[
\begin{equation*}
    \mathbf D = \varepsilon \mathbf E \text{ and } \mathbf B = \mu \mathbf H
\end{equation*}
\]`

where `\(\varepsilon\)` and `\(\mu\)` are the electrical permittivity (farads/meter) and magnetic permeability (henrys/meter) of our material. 

This is convenient because it allows us to rewrite Faraday's and Ampere's laws in terms of only 4 fields: `\(\mathbf E\)`, `\(\mathbf H\)`, and our source fields `\(\mathbf{\hat J}\)` and `\(\mathbf{\hat M}\)`:

`\[ \begin{aligned}
  \frac{\partial \mathbf H}{\partial t} & = - \frac{1}{\mu} \nabla \times \mathbf E - \frac{1}{\mu}\left(\mathbf{\hat M} + \sigma^* \mathbf H \right) \\
  \frac{\partial \mathbf E}{\partial t} & = \frac{1}{\varepsilon} \nabla \times \mathbf H - \frac{1}{\varepsilon}\left(\mathbf{\hat J} + \sigma \mathbf E \right)
\end{aligned} \]`

Today we'll be working in rectangular coordinates, so that each field `\(\mathbf F\)` may be written as a vector `\(\mathbf F = (F_1(x,y,z,t), F_2(x,y,z,t), F_3(x,y,z,t))\)`. We get six partial differential equations:

Faraday's law:

`\[ \begin{aligned}
\frac{\partial H_1}{\partial t} & = \frac{1}{\mu}\left( \frac{\partial E_2}{\partial z} - \frac{\partial E_3}{\partial y} - \left( \hat M_1 + \sigma^* H_1 \right) \right) \\
\frac{\partial H_2}{\partial t} & = \frac{1}{\mu}\left( \frac{\partial E_3}{\partial x} - \frac{\partial E_1}{\partial z} - \left( \hat M_2 + \sigma^* H_2 \right) \right) \\
\frac{\partial H_3}{\partial t} & = \frac{1}{\mu}\left( \frac{\partial E_1}{\partial y} - \frac{\partial E_2}{\partial x} - \left( \hat M_3 + \sigma^* H_3 \right) \right) 
\end{aligned} \]`

Ampere's law:

`\[ \begin{aligned}
\frac{\partial E_1}{\partial t} & = \frac{1}{\varepsilon}\left( \frac{\partial H_3}{\partial y} - \frac{\partial H_2}{\partial z} - \left( \hat J_1 + \sigma E_1 \right) \right) \\
\frac{\partial E_2}{\partial t} & = \frac{1}{\varepsilon}\left( \frac{\partial H_1}{\partial z} - \frac{\partial H_3}{\partial x} - \left( \hat J_2 + \sigma E_2 \right) \right) \\
\frac{\partial E_3}{\partial t} & = \frac{1}{\varepsilon}\left( \frac{\partial H_2}{\partial x} - \frac{\partial H_1}{\partial y} - \left( \hat J_3 + \sigma E_3 \right) \right) 
\end{aligned} \]`


The finite differences
----------------------

The rest of the idea works like this: we interpret the partial derivative operators (such as `\(\frac{\partial}{\partial t}\)`, `\(\frac{\partial}{\partial x}\)`, and the rest) as _finite central difference_ operators. Taking the `\(t\)` parameter as an example, while we would normally write

`\[
\frac{\partial F}{\partial t}(x, y, z, t) = \lim_{\Delta t \to 0} \frac{F(x, y, z, t+\Delta t) - F(x, y, z, t)}{\Delta t} \mathrm,
\]`

we instead fix a value `\(\Delta t > 0\)` and write

`\[
\frac{\partial F}{\partial t}(x, y, z, t) = \frac{F(x, y, z, t + \Delta t/2) - F(x, y, z, t - \Delta t/2)}{\Delta t} \mathrm.
\]`

Here we're interpreting the partial derivative as a _central difference operator_. In essence, we have taken our PDE and reverted it into a statement about slopes, just as we would do when preparing EM homework for middle school students.

In what follows it is best to compactify our notation. Let `\(\Delta x, \Delta y, \Delta z, \Delta t\)` be positive. For functions `\(F : \mathbb R^4 \to \mathbb R\)`, write

`\[
    F|^n_{i,j,k} = F(i\,\Delta x, j\,\Delta y, k\,\Delta z, n\,\Delta t) \mathrm.
\]`

With our notation and our differential operators in hand, we proceed to rewrite Faraday's and Ampere's laws. For instance, at `\((i\,\Delta x, j\,\Delta y, k\,\Delta z, n\,\Delta t)\)`, the first equation for Ampere's law becomes

`\[
  \begin{align*}
    \left.\frac{\partial E_1}{\partial t}\right|^n_{i,j,k}
        = & \left.\frac{1}{\varepsilon}\left(
                \frac{\partial H_3}{\partial y}
                - \frac{\partial H_2}{\partial z}
                - \left( \hat J_1 + \sigma E_1 \right)
            \right)\right|^n_{i,j,k} \\
    \frac{E_1|^{n+\frac{1}{2}}_{i,j,k} - E_1|^{n-\frac{1}{2}}_{i,j,k}}{\Delta t}
        = & \frac{1}{\varepsilon_{i,j,k}}\left(
                \frac{H_3|^n_{i,j+\frac{1}{2},k} - H_3|^n_{i,j-\frac{1}{2},k}}{\Delta y} 
                - \frac{H_2|^n_{i,j,k+\frac{1}{2}} - H_2|^n_{i,j,k-\frac{1}{2}}}{\Delta z}\right) \\
          &     - \frac{1}{\varepsilon_{i,j,k}}\left( \hat J_1|^n_{i,j,k} + \sigma E_1|^n_{i,j,k} \right)
  \end{align*}
\]`

We now make some observations:

* The term `\(E_1|^{n+\frac{1}{2}}_{i,j,k}\)` (appearing on the left-hand side) is further into the future than the other terms in the equation. We can therefore use the equation to forward time-step our simulation of `\(E_1\)`. The same thing will happen for `\(E_2, E_3\)` when we evaluate the rest of Ampere's Law, and for `\(H_1, H_2, H_3\)` when we evaluate Faraday's law.
* The differentials for `\(y\)` and `\(z\)` cause `\(H_3\)` and `\(H_2\)` to be sampled at half-integral values (such as `\(i,j+1/2,k\)` in the case of `\(H_3\)`). Hence if we want to evaluate `\(E_1\)` at the integral point `\((i,j,k)\)`, we'll need to sample some of the `\(\mathbf H\)`-field components at points with half-integral coordinates.
* The equation samples `\(E_1\)` at both integral and half-integral values for time.

One could take these equations and proceed to simulate the evolution of each of the field components at every integral- and half-integral point in space and time, and everything would work as desired.

However, if we are careful in our choice of where to simulate each field component (noting that, for instance, we need not sample `\(E_1\)` and `\(E_2\)` at the same points in space), we can reduce the density of our simulation enormously, without giving up much in accuracy.

Yee's lattice
-------------

The textbook approach is due to [Kane Yee (1966)](http://adsabs.harvard.edu/abs/1966ITAP...14..302Y). We do two things.

First, we rewrite our equations such that the `\(\mathbf E\)`-field is computed only at half-integral times, while the `\(\mathbf H\)`-field is only computed at integral times. This means the simulation proceeds by alternately applying the relations derived from Faraday's and Ampere's laws. To do this, one must deal with the fact that, as written thus-far, the equations make mention of integral and half-integral time sampling for every field component.

The solution is to use a cheap approximation. For instance, to eliminate the presence of `\(E_1|^n_{i,j,k}\)` above, we could employ the following:

`\[
    E_1|^n_{i,j,k} \approx \frac{1}{2}\left( E_1|^{n+\frac{1}{2}}_{i,j,k} + E_1|^{n-\frac{1}{2}}_{i,j,k} \right) \mathrm.
\]`

We then chunk up 3-space into blocks of dimension `\(\Delta x \times \Delta y \times \Delta z\)`. Each block represents one unit of simulation that we're going to perform. Each block contains 1 sample point for each field component `\(E_1, E_2, E_3, H_1, H_2, H_3\)`. In _Computational Electrodynamics_, a scheme is chosen where each field component is sampled according to the points in a corresponding lattice:

`\[
\begin{align}
\mathcal L_{E_1} & = \left\{ (i,j+1/2,k+1/2) \,|\, i,j,k \in \mathbb Z \right\} \\
\mathcal L_{E_2} & = \left\{ (i-1/2,j,k+1/2) \,|\, i,j,k \in \mathbb Z \right\} \\
\mathcal L_{E_3} & = \left\{ (i-1/2,j+1/2,k) \,|\, i,j,k \in \mathbb Z \right\} \\
\mathcal L_{H_1} & = \left\{ (i-1/2,j,k) \,|\, i,j,k \in \mathbb Z \right\} \\
\mathcal L_{H_2} & = \left\{ (i,j+1/2,k) \,|\, i,j,k \in \mathbb Z \right\} \\
\mathcal L_{H_3} & = \left\{ (i,j+1,k+1/2) \,|\, i,j,k \in \mathbb Z \right\} \\
\end{align}
\]`

So you can see that the field component `\(H_2\)` is only sampled at points in space of the form `\((i\Delta x, (j+1/2)\Delta y, k\Delta z)\)`. This is substantially less dense than the naive scheme where we needed to sample every field component at every integral- and half-integral point in space!

If you finish working out the algebra, this selection of sample points should leave you good to go. At least, until you need to deal with boundary conditions. But that's a story for another time.


