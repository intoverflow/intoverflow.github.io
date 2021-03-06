---
layout: post
title: Hello VST, hello Verifiable C
---

<center><h1 style="color: red; background-color: yellow;">draft draft draft draft draft</h1></center>

On today's show:

* Table of Contents
{:toc}

Files you can download:

* [<code>strncat.c</code>](/assets/strncat/strncat.c)
* [<code>strncat.v</code>](/assets/strncat/strncat.v)
* [<code>verif_strncat.v</code>](/assets/strncat/verif_strncat.v)

Introduction
============

This post is about writing formally verified C code. If you're writing formally verified software in C, there are three things you're gonna want:

* A mathematical meta-language for defining and reasoning about an abstract model of your code;
* A "program logic" for C -- that is, a meta-language within-which you may reason about the behavior of C code, and relate it to your mathematical meta-language;
* A C compiler which preserves whatever theorems you've proven in your program logic.

For instance, if you are formally verifying a program which sieves for prime numbers, you'd want:

* A model of the integers, with a definition of primality;
* Some kind of argument relating your code's behavior to this model;
* A compiler whose output relates to your model the same as your C code did.

There aren't a lot of tool suites which support this type of work flow. In industry, there are many tools for reasoning formally about software; but these tools tend to be closed-source and tres riche, making them ill-suited for Internet-scale infrastructure.


A new hope?
-----------

Today we'll look at one approach to formally verifying C code: [Coq](http://coq.inria.fr) + [CompCert](http://compcert.inria.fr) + [VST](http://vst.cs.princeton.edu/) + [Verifiable C](http://vst.cs.princeton.edu/veric). Coq is a proof agent; it provides the mathematical meta-language. VST and Verifiable C provide the program logic. CompCert is the compiler.

Coq and CompCert have been described all over Internet. For us, the take-away is that CompCert is written in Coq, and has been shown not to introduce any bugs during the compilation process (versus, say, GCC, which is known to introduce bugs into programs).

VST ([Verified Software Toolchain](http://vst.cs.princeton.edu/)) is a framework for using [separation logic](http://en.wikipedia.org/wiki/Separation_logic) to analyze the behavior of programs with global mutable state. Presently, the "killer app" for VST is [Verifiable C](http://vst.cs.princeton.edu/veric/), a program logic for a psudo-C language ("C light," which happens to be an intermediate language used by CompCert).

The nice thing about Verifiable C is that its program logic has been formally shown (again, in Coq) to be compatible with the semantics defined by CompCert.

So with this tool chain, we can write our code in more-or-less ordinary C style, prove theorems about our code in Coq using the Verifiable C program logic, and when we compile using CompCert we'll know that (a) CompCert didn't introduce any bugs into our compiled program and (b) our compiled program satisfies an appropriate version of the theorems we proved earlier.

Sounds very nice to me, let's get started.


Installing CompCert and VST
===========================

At time of writing, the latest release of VST is Version 1.4, which is compatible with CompCert 2.3pl2.

Download link for CompCert 2.3pl2: [http://compcert.inria.fr/release/compcert-2.3pl2.tgz](http://compcert.inria.fr/release/compcert-2.3pl2.tgz), or, if that's stale, you can get a copy from me: [http://intoverflow.github.io/assets/compcert-2.3pl2.tgz](http://intoverflow.github.io/assets/compcert-2.3pl2.tgz).

Download link for VST 1.4: [http://vst.cs.princeton.edu/download/vst-1.4.tgz](http://vst.cs.princeton.edu/download/vst-1.4.tgz), or, if that's stale, you can get a copy from me: [http://intoverflow.github.io/assets/vst-1.4.tgz](http://intoverflow.github.io/assets/vst-1.4.tgz).

So now we get started:

<div style="background-color: #D6EBFF;">
<pre>
<i>[tcarstens@weibel ~]$</i> <b>mkdir verifiable-c</b>
<i>[tcarstens@weibel ~]$</i> <b>cd verifiable-c/</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>wget --quiet "http://compcert.inria.fr/release/compcert-2.3pl2.tgz"</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>wget --quiet "http://vst.cs.princeton.edu/download/vst-1.4.tgz"</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>md5sum *</b>
f97700e91163e6fbdb645721e2c1350f  compcert-2.3pl2.tgz
d6a2aff5a454ffc421e18dbda690e930  vst-1.4.tgz
<i>[tcarstens@weibel verifiable-c]$</i> <b>sha256sum *</b>
a8626962e1aa0c7ac566d799c4b4c588a2bbc9e47fd5a2bfae8152438caf04b3  compcert-2.3pl2.tgz
68a0ee84e3800c4fba933a9fd8a36fe4416ef758e80ec0a8416b3d984144aa1c  vst-1.4.tgz
<i>[tcarstens@weibel verifiable-c]$</i> <b>tar -xf compcert-2.3pl2.tgz</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>tar -xf vst-1.4.tgz</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>ls -F</b>
compcert-2.3pl2/  compcert-2.3pl2.tgz  vst/  vst-1.4.tgz
<i>[tcarstens@weibel verifiable-c]$</i>
</pre>
</div>

So far so good. Now we inspect our host for dependencies. In my case, I'm running Linux x86-64, with the intent to have CompCert target ia32-linux. You'll note that I have two gcc's installed; when building CompCert, I'll need to specify which gcc to use.

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel verifiable-c]$</i> <b>uname -a</b>
Linux weibel 3.10.9-1-ARCH #1 SMP PREEMPT Wed Aug 21 13:49:35 CEST 2013 x86_64 GNU/Linux
<i>[tcarstens@weibel verifiable-c]$</i> <b>cat /proc/cpuinfo | grep "model name"</b>
model name	: Intel(R) Core(TM) i7-3520M CPU @ 2.90GHz
model name	: Intel(R) Core(TM) i7-3520M CPU @ 2.90GHz
model name	: Intel(R) Core(TM) i7-3520M CPU @ 2.90GHz
model name	: Intel(R) Core(TM) i7-3520M CPU @ 2.90GHz
<i>[tcarstens@weibel verifiable-c]$</i> <b>gcc -v</b>
<i>...(output elided)...</i>
Target: x86_64-unknown-linux-gnu
<i>...(output elided)...</i>
gcc version 4.8.1 20130725 (prerelease) (GCC)
<i>[tcarstens@weibel verifiable-c]$</i> <b>arm-none-eabi-gcc -v</b>
<i>...(output elided)...</i>
Target: arm-none-eabi
<i>...(output elided)...</i>
gcc version 4.9.0 (Arch Repository) 
<i>[tcarstens@weibel verifiable-c]$</i> <b>coqc -v</b>
The Coq Proof Assistant, version 8.4pl3 (March 2014)
compiled on Mar 25 2014 01:27:43 with OCaml 4.01.0
<i>[tcarstens@weibel verifiable-c]$</i> <b>file `which coqc`</b>
/usr/bin/coqc: ELF 64-bit LSB  executable, x86-64, version 1 (SYSV), dynamically linked (uses shared libs), for GNU/Linux 2.6.32, BuildID[sha1]=adcbf1ed229ca82e8a43c124c15a32278de4dee9, stripped
<i>[tcarstens@weibel verifiable-c]$</i>
</pre>
</div>

Very good, let's build CompCert. Now as it happens, CompCert depends on GCC at run-time (it uses the GCC preprocessor). So we need to tell CompCert which GCC to build for. By default, it will assume `gcc`, which happens to be what I want because I'm targetting ia32-linux. If I were targeting arm-eabi, I'd want to use `arm-none-eabi-gcc`, and to do that I'd toss in an extra `-toolprefix arm-none-eabi-` flag to the configure script.

<div style="background-color: #D6EBFF;">
<pre>
<i>[tcarstens@weibel verifiable-c]$</i> <b>pushd compcert-2.3pl2</b>
~/verifiable-c/compcert-2.3pl2 ~/verifiable-c
<i>[tcarstens@weibel compcert-2.3pl2]$</i> <b>./configure ia32-linux -no-runtime-lib &> ../compcert-2.3pl2.configurelog</b>
<i>[tcarstens@weibel compcert-2.3pl2]$</i> <b>cat ../compcert-2.3pl2.configurelog</b>
Testing assembler support for CFI directives... yes
Testing Coq... version 8.4pl3 -- good!
Testing OCaml... version 4.01.0 -- good!
Testing Menhir... version 20140422 -- good!

CompCert configuration:
    Target architecture........... ia32
    Application binary interface.. standard
    OS and development env........ linux
    C compiler.................... gcc -m32
    C preprocessor................ gcc -m32 -U__GNUC__ -E
    Assembler..................... gcc -m32 -c
    Assembler supports CFI........ true
    Assembler for runtime lib..... gcc -m32 -c
    Linker........................ gcc -m32
    Math library.................. -lm
    Binaries installed in......... /usr/local/bin
    Runtime library provided...... false
    Library files installed in.... /usr/local/lib/compcert
    cchecklink tool supported..... false

If anything above looks wrong, please edit file ./Makefile.config to correct.

<i>[tcarstens@weibel compcert-2.3pl2]$</i> <b>time make -j 6 all &> ../compcert-2.3pl2.makelog</b>
<i>...(go get some coffee, or open another terminal and tail -f ../compcert-2.3pl2.makelog)...</i>

real	22m17.246s
user	79m14.576s
sys	1m28.580s
<i>[tcarstens@weibel compcert-2.3pl2]$</i> <b>time make -j 6 clightgen &> ../compcert-2.3pl2.makelog-clightgen</b>

real	0m1.732s
user	0m1.600s
sys	0m0.090s
<i>[tcarstens@weibel compcert-2.3pl2]$</i> <b>./clightgen --help</b>
The CompCert Clight generator
Usage: clightgen [options] &lt;source files>
Recognized source files:
  .c             C source file
Processing options:
  -E             Preprocess only, send result to standard output
Preprocessing options:
  -I&lt;dir>        Add &lt;dir> to search path for #include files
  -D&lt;symb>=&lt;val> Define preprocessor symbol
  -U&lt;symb>       Undefine preprocessor symbol
  -Wp,&lt;opt>      Pass option &lt;opt> to the preprocessor
Language support options (use -fno-&lt;opt> to turn off -f&lt;opt>) :
  -fbitfields    Emulate bit fields in structs [off]
  -flongdouble   Treat 'long double' as 'double' [off]
  -fstruct-return  Emulate returning structs and unions by value [off]
  -fvararg-calls Emulate calls to variable-argument functions [on]
  -fpacked-structs  Emulate packed structs [off]
  -fall          Activate all language support options above
  -fnone         Turn off all language support options above
Tracing options:
  -dparse        Save C file after parsing and elaboration in &lt;file>.parse.c
  -dc            Save generated Compcert C in &lt;file>.compcert.c
  -dclight       Save generated Clight in &lt;file>.light.c
General options:
  -v             Print external commands before invoking them
<i>[tcarstens@weibel compcert-2.3pl2]$</i> <b>./ccomp --help</b>
The CompCert C verified compiler, version 2.3pl2
Usage: ccomp [options] &lt;source files>
<i>...(output elided)...</i>
<i>[tcarstens@weibel compcert-2.3pl2]$</i> <b>popd</b>
~/verifiable-c
<i>[tcarstens@weibel verifiable-c]$</i>
</pre>
</div>

Sweet. Now we can build VST. You'll need to create a <code>vst/CONFIGURE</code> file pointing to your CompCert source directory.

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel verifiable-c]$</i> <b>pushd vst</b>
~/verifiable-c/vst ~/verifiable-c
<i>[tcarstens@weibel vst]$</i> <b>echo "COMPCERT=../compcert-2.3pl2" > CONFIGURE</b>
<i>[tcarstens@weibel vst]$</i> <b>cat CONFIGURE</b>
COMPCERT=../compcert-2.3pl2
<i>[tcarstens@weibel vst]$</i> <b>time make -j 6 &> ../vst.makelog</b>
<i>...(go get some lunch, or open another terminal and tail -f ../vst.makelog)...</i>
real	33m20.637s
user	83m42.863s
sys	0m39.973s
<i>[tcarstens@weibel vst]$</i> <b>coqtop `cat .loadpath` -l progs/verif_sumarray.v</b>
Welcome to Coq 8.4pl3 (March 2014)
&lt;W> Grammar extension: in [constr:operconstr] some rule has been masked

<i>Coq &lt;</i> <b>Print sumarray_spec.</b>
sumarray_spec = 
(_sumarray:ident,
(WITH  p : val * share * (Z -> val), size : Z PRE  [
 (_a, tptr tint), (_n, tint)]
 (let (p0, contents) := p in
  let (a0, sh) := p0 in
  PROP  (0 &lt;= size &lt;= Int.max_signed;
  forall i : Z, 0 &lt;= i &lt; size -> is_int (contents i))
  LOCAL  (`(eq a0) (eval_id _a); `(eq (Vint (Int.repr size))) (eval_id _n);
  `isptr (eval_id _a))
  SEP  (`(array_at tint sh contents 0 size) (eval_id _a))) POST  [tint]
 (let (p0, contents) := p in
  let (a0, sh) := p0 in
  local
    (`(eq (Vint (fold_range (add_elem contents) Int.zero 0 size))) retval) &&
  `(array_at tint sh contents 0 size a0)))
:funspec)
     : ident * funspec

<i>Coq &lt;</i> <b>Quit.</b>
<i>[tcarstens@weibel vst]$</i> <b>popd</b>
~/verifiable-c
<i>[tcarstens@weibel verifiable-c]$</i>
</pre>
</div>

Excellent. As you can see, we've made it to a point where we can work with the VST sample programs (in the case above, <code>sumarray</code>).

Now let's write and verify something of our own.


<code>strncat</code> in Verifiable C
====================================

First lets set up our environment. While you weren't looking, I authored <code>.loadpath</code> and <code>strncat.c</code> (you can download the latter here: [<code>strncat.c</code>](/assets/strncat/strncat.c)). The <code>.loadpath</code> file is adapted from a file of the same name in the <code>VST</code> directory, which is generated when building VST. You can see it getting written in my VST build log above.

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel strncat]$</i> <b>ln -s ~/verifiable-c/compcert-2.3pl2 compcert</b>
<i>[tcarstens@weibel strncat]$</i> <b>ln -s ~/verifiable-c/vst vst</b>
<i>[tcarstens@weibel strncat]$</i> <b>ls -Fa</b>
./  ../  .loadpath  compcert@  strncat.c  vst@
<i>[tcarstens@weibel strncat]$</i> <b>cat .loadpath</b>
-I vst/msl -as msl -I vst/sepcomp -as sepcomp -I vst/veric -as veric -I vst/floyd -as floyd -I vst/progs -as progs -R compcert -as compcert
<i>[tcarstens@weibel strncat]$</i> <b>cat strncat.c</b>
typedef unsigned int size_t;

size_t strlen(const unsigned char *s) {
  size_t i;
  unsigned char c;

  i = 0;
  c = s[i];
  while ('\0' != c) {
    i++;
    c = s[i];
  }

  return i;
}

unsigned char *strncat(unsigned char *dest, const unsigned char *src, size_t n) {
  size_t dest_len = strlen(dest);
  size_t i;

  for (i = 0; i < n && src[i] != 0; i++)
    dest[dest_len + i] = src[i];
  dest[dest_len + i] = 0;

  return dest;
}

<i>[tcarstens@weibel strncat]$</i>
</pre>
</div>

We now generate a Coq file <code>strncat.v</code> which contains abstract-syntax for a Clight version of <code>strncat.c</code> (which you can download here: [<code>strncat.v</code>](/assets/strncat/strncat.v)):

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel strncat]$</i> <b>compcert/clightgen strncat.c</b>
<i>[tcarstens@weibel strncat]$</i> <b>cat strncat.v</b>
Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _c : ident := 32%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition _strncat : ident := 38%positive.
Definition ___builtin_fmadd : ident := 24%positive.
Definition ___builtin_fmax : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _n : ident := 36%positive.
Definition _i : ident := 31%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___builtin_fnmadd : ident := 26%positive.
Definition ___builtin_bswap32 : ident := 19%positive.
Definition _main : ident := 39%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition _dest_len : ident := 37%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_read16_reversed : ident := 28%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_fsqrt : ident := 21%positive.
Definition ___builtin_bswap : ident := 18%positive.
Definition ___builtin_annot : ident := 9%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_fnmsub : ident := 27%positive.
Definition _strlen : ident := 33%positive.
Definition ___builtin_fmsub : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition _dest : ident := 34%positive.
Definition ___builtin_read32_reversed : ident := 29%positive.
Definition _src : ident := 35%positive.
Definition _s : ident := 30%positive.
Definition ___builtin_fmin : ident := 23%positive.
Definition ___builtin_bswap16 : ident := 20%positive.
Definition _dest_len' : ident := 40%positive.


Definition f_strlen := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_c, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sset _c
      (Ecast
        (Ederef
          (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tuint)
            (tptr tuchar)) tuchar) tuchar))
    (Ssequence
      (Swhile
        (Ebinop One (Econst_int (Int.repr 0) tint) (Etempvar _c tuchar) tint)
        (Ssequence
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))
          (Sset _c
            (Ecast
              (Ederef
                (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tuint)
                  (tptr tuchar)) tuchar) tuchar))))
      (Sreturn (Some (Etempvar _i tuint))))))
|}.

Definition f_strncat := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr tuchar)) :: (_src, (tptr tuchar)) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_dest_len, tuint) :: (_i, tuint) :: (41%positive, tint) ::
               (_dest_len', tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _dest_len')
      (Evar _strlen (Tfunction (Tcons (tptr tuchar) Tnil) tuint cc_default))
      ((Etempvar _dest (tptr tuchar)) :: nil))
    (Sset _dest_len (Etempvar _dest_len' tuint)))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tuint)
                           tint)
              (Ssequence
                (Sset 41%positive
                  (Ecast
                    (Ebinop One
                      (Ederef
                        (Ebinop Oadd (Etempvar _src (tptr tuchar))
                          (Etempvar _i tuint) (tptr tuchar)) tuchar)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset 41%positive (Ecast (Etempvar 41%positive tbool) tint)))
              (Sset 41%positive (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar 41%positive tint) Sskip Sbreak))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _dest (tptr tuchar))
                (Ebinop Oadd (Etempvar _dest_len tuint) (Etempvar _i tuint)
                  tuint) (tptr tuchar)) tuchar)
            (Ederef
              (Ebinop Oadd (Etempvar _src (tptr tuchar)) (Etempvar _i tuint)
                (tptr tuchar)) tuchar)))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _dest (tptr tuchar))
            (Ebinop Oadd (Etempvar _dest_len tuint) (Etempvar _i tuint)
              tuint) (tptr tuchar)) tuchar) (Econst_int (Int.repr 0) tint))
      (Sreturn (Some (Etempvar _dest (tptr tuchar)))))))
|}.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin ___builtin_annot
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin ___builtin_va_start
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin ___builtin_va_arg
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin ___builtin_va_copy
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin ___builtin_va_end
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external ___compcert_va_int32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external ___compcert_va_int64
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external ___compcert_va_float64
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin ___builtin_bswap
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin ___builtin_bswap32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin ___builtin_bswap16
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin ___builtin_fsqrt
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin ___builtin_fmax
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin ___builtin_fmin
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin ___builtin_fmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin ___builtin_fmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin ___builtin_fnmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin ___builtin_fnmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin ___builtin_read16_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin ___builtin_write16_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) :: (_strlen, Gfun(Internal f_strlen)) ::
 (_strncat, Gfun(Internal f_strncat)) :: nil);
prog_main := _main
|}.

<i>[tcarstens@weibel strncat]$ </i>
</pre>
</div>

Lovely. Now we need to specify its behavior, and prove it conforms to that specification.




A formal specification for <code>strncat</code>
-----------------------------------------------

An informal specification for <code>strncat</code> is given in <code>man 3 strncat</code>:

*<code>char *strcat(char *dest, const char *src);</code>*

*<code>char *strncat(char *dest, const char *src, size_t n);</code>*


*The <code>strcat()</code> function appends the <code>src</code> string to the <code>dest</code> string, overwriting the terminating null byte (<code>'\0'</code>) at the end of <code>dest</code>,  and  then adds  a  terminating  null  byte.  The strings may not overlap, and the <code>dest</code> string must have enough space for the  result.  If <code>dest</code> is  not large  enough, program behavior is unpredictable; **buffer overruns are a favorite avenue for attacking secure programs.***

*The <code>strncat()</code> function is similar, except that*

* *it will use at most <code>n</code> bytes from <code>src</code>; and*
* *<code>src</code> does not need to be null-terminated if it contains <code>n</code> or more bytes.*

*As  with <code>strcat()</code>,  the resulting string in <code>dest</code> is always null-terminated.*

*If <code>src</code> contains <code>n</code> or more bytes, <code>strncat()</code> writes <code>n+1</code> bytes to <code>dest</code>  (<code>n</code> from  <code>src</code> plus the terminating null byte).  Therefore, the size of <code>dest</code> must be at least <code>strlen(dest)+n+1</code>.*

Our present task is to produce a formal version of this specification in Coq. To do so, we'll need a *meta-theory of strings*, which we will use to abstractly model the behavior of <code>strncat</code>.

Coq already has a [<code>string</code>](http://coq.inria.fr/stdlib/Coq.Strings.String.html) type, which represents strings as lists of [<code>ascii</code>](http://coq.inria.fr/stdlib/Coq.Strings.Ascii.html) values, which themselves are represented as 8-tuples of [<code>bool</code>](http://coq.inria.fr/stdlib/Coq.Init.Datatypes.html#bool)s. The Coq standard library includes functions for computing string length, concatenating strings, and obtaining sub-strings. In short, it should have everything we need, so we may as well use it as our meta-theory.

So now we may begin writing our specification. Let us first specify the behavior of <code>strlen</code>, as our <code>strncat</code> specification will surely make use of it.

Ok, so let's compile <code>strncat.v</code> and fire up CoqIDE to begin authoring and proving a specification:

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel strncat]$</i> <b>time coqc `cat .loadpath` strncat.v</b>

real	0m2.107s
user	0m1.900s
sys	0m0.200s
<i>[tcarstens@weibel strncat]$</i> <b>coqide `cat .loadpath` verif_strncat.v</b>
</pre>
</div>

At this point we've (a) setup our environment so that we can use CompCert and VST, (b) compiled our Coq representation of <code>strncat.c</code> (meaning that other Coq code can open this module and work with its definitions), and (c) launched CoqIDE with a new file <code>verif_strncat.v</code>.

Let's begin authoring <code>verif_strncat.v</code>. (Here's a download link for [<code>verif_strncat.v</code>](/assets/strncat/verif_strncat.v)). We'll use this soothing yellowish-cream background color to indicate the contents of this file, concatenating as we go. First we import some libraries:

<div style="background-color: #FFFFDB;">
<pre style="white-space: pre-wrap;">
Require Import floyd.proofauto.

Require Import Coq.Strings.Ascii.

</pre>
</div>

Now we'll make some definitions which move us towards relating Clight values to our meta-theory of strings. For now, we only need concern ourselves with specifying what we mean by a (Clight) "ascii" value or a (Clight) "null-terminated ascii string".

<div style="background-color: #FFFFDB;">
<pre style="white-space: pre-wrap;">
Inductive ascii : val -> Prop :=
  | is_ascii c: (0 <= Int.intval c < 128) -> ascii (Vint c).

Inductive ascii_not_nil : val -> Prop :=
  | is_ascii_not_nil c: (0 < Int.intval c < 128) -> ascii_not_nil (Vint c).

Lemma ascii_not_nil_is_ascii: forall v, ascii_not_nil v -> ascii v.
Proof. intros. inversion H. apply is_ascii. omega. Qed.

Inductive ascii_string (contents: Z -> val) (len size: Z) : Prop :=
  | is_ascii_string:
     (0 <= len < size)
     -> (forall i, 0 <= i < len -> ascii_not_nil (contents i))
     -> contents len = Vint Int.zero
     -> ascii_string contents len size.

Lemma ascii_string_is_int:
  forall contents len size,
   ascii_string contents len size
   -> forall i, 0 <= i <= len -> is_int (contents i).
Proof.
  intros.
  destruct (Z_dec i len) eqn:?.
  + destruct s ; try omega.
    destruct H.
    assert (ascii_not_nil (contents i)) as ann by (apply H1 ; omega).
    inversion ann.
    simpl ; trivial.
  + inversion H.
    subst.
    rewrite H3.
    simpl ; trivial.
Qed.

</pre>
</div>

Now we're set to write our specification for <code>strlen</code>. Try to read the specification and figure out what it means. I'll offer a quick hint: think of <code>_s</code> as the argument to <code>strlen</code>, and <code>s0</code> as an abstract representative of that argument.

<div style="background-color: #FFFFDB;">
<pre>
Require Import strncat.

Local Open Scope logic.

Definition strlen_spec :=
 DECLARE _strlen
  WITH s0: val, sh : share, contents : Z -> val, len: Z, size: Z
  PRE [ _s OF (tptr tuchar) ]
          PROP (0 < size <= Int.max_signed;
                ascii_string contents len size)
          LOCAL (`(eq s0) (eval_id _s); `isptr (eval_id _s))
          SEP (`(array_at tuchar sh contents 0 size s0))
  POST [ tuint ]
        local (`(eq (Vint (Int.repr len))) retval)
              && `(array_at tuchar sh contents 0 size s0).

</pre>
</div>

This specification says that <code>strlen</code> takes an argument <code>_s</code> which is an array of <code>char</code>s of size <code>size</code>. It posits that this array is a null-terminated ascii string of length <code>len</code>, in the sense described above (see our <code>ascii_string</code> definition).

It says that <code>strlen</code> returns a machine <code>int</code> which is equivalent to <code>len</code> (modulo <code>8*sizeof(int)</code>).

Lastly, it says that <code>strlen</code> does not modify the data pointed-to by <code>_s</code>.

A formal proof that our <code>strlen</code> is correct
------------------------------------------------


First we bundle up all of our definitions and specifications:

<div style="background-color: #FFFFDB;">
<pre>
Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=  strlen_spec :: nil.

</pre>
</div>

Now we can state and prove a lemma about <code>strlen</code> meeting its specification. Note that I got stuck near the end and cheated with an "admit". I admit it, I got tired!

<div style="background-color: #FFFFDB;">
<pre>
Lemma body_strlen: semax_body Vprog Gprog f_strlen strlen_spec.
Proof.
  start_function.
  set (H_ascii_string := H0).
  destruct H0 as [ zero_lte_len_lt_size H_ascii_not_nil H_contents_len ].
  forward (* i = 0; *).
  forward. (* c = s[i]; *)
  { entailer!.
    destruct (zeq 0 len).
    + subst ; rewrite H_contents_len ; simpl ; trivial.
    + assert (ascii_not_nil (contents 0)) as ann
         by (apply H_ascii_not_nil; omega).
      inv ann; simpl; auto.
  }
  set (strlen_Inv :=
    EX i': Z,
    (PROP ( 0 <= i' <= len )
     LOCAL ( `(eq s0) (eval_id _s)
           ; `(eq (Vint (Int.repr i'))) (eval_id _i)
           ; `(eq (contents i')) (eval_id _c)
           )
     SEP ( `(array_at tuchar sh contents 0 size) (eval_id _s) )
    ) ).
  set (strlen_Post :=
    (PROP ( )
     LOCAL ( `(eq s0) (eval_id _s)
           ; `(eq (Vint (Int.repr len))) (eval_id _i)
           )
     SEP ( `(array_at tuchar sh contents 0 size) (eval_id _s) )
    ) ).
  forward_while strlen_Inv strlen_Post; unfold strlen_Inv, strlen_Post in * ; clear strlen_Inv strlen_Post.
  (* Prove that current precondition implies loop invariant *)
  { apply exp_right with 0.
    entailer!.
    rewrite H0.
    normalize.
    destruct (zeq 0 len).
    + subst ; rewrite H_contents_len ; simpl.
      normalize.
    + assert (ascii_not_nil (contents 0)) as contents_0_ascii_nn.
      { apply H_ascii_not_nil ; omega. }
      assert (is_int (contents 0)) as contents_0_is_int.
      { apply ascii_string_is_int with len size ; try omega.
        apply H_ascii_string.
      }
      destruct (contents 0) ; simpl in contents_0_is_int ; try contradiction.
      destruct contents_0_ascii_nn.
      simpl.
      (* *)
      admit.
  }
  (* Prove that loop invariant implies typechecking condition *)
  { entailer!. }
  (* Prove that invariant && not loop-cond implies postcondition *)
  { entailer!.
    replace len with i' ; trivial.
    apply Z.le_lteq in H1 ; destruct H1 ; try assumption.
    (* now we go for the contradiction *)
    rewrite negb_false_iff in H2.
    apply int_eq_e in H2.
    assert (ascii_not_nil (contents i')) as H_contents_i'.
    { apply H_ascii_not_nil. omega. }
    destruct H_contents_i'.
    inversion H3 ; subst ; simpl in *.
    omega.
  }
  (* Prove that loop body preserves invariant *)
  { forward (* i++; *).
    forward (* c = s[i]; *).
    + entailer!.
      { (* is_int (contents (i' + 1)) *)
        assert (i' < len) as H_i'_len.
        { apply Z.le_lteq in H1 ; destruct H1 ; subst ; try assumption.
          rewrite H_contents_len in H4.
          inversion H4 ; subst.
          compute in H3 ; inversion H3.
        }
        assert (is_int (contents (i' + 1))) as Q.
        { apply ascii_string_is_int with len size.
          + apply H_ascii_string.
          + omega.
        }
        destruct (contents (i' + 1)) ; simpl in * ; try contradiction ; trivial.
      }
      { (* 0 <= i' + 1 < size *)
        assert (i' < len) ; try omega.
        apply Z.le_lteq in H1.
        destruct H1 ; trivial ; subst.
        rewrite H_contents_len in H4 ; inversion H4 ; subst.
        compute in H3 ; inversion H3.
      }
    + entailer!.
      apply exp_right with (i' + 1).
      entailer!.
      { (* i' + 1 <= len *)
        assert (contents i' <> Vint Int.zero).
        { intro Q ; rewrite Q in H4.
          compute in H4 ; inversion H4.
        }
        apply Z.le_lteq in H1.
        destruct H1 ; subst ; try omega ; congruence.
      }
      { (* contents (i' + 1) = Vint _id *)
        rewrite H2 ; normalize.
        (* *)
        admit.
      }
  }
  (* loop is done, continue with rest of proof *)
  forward (* return i; *).
Qed.

</pre>
</div>


A formal proof that our <code>strncat</code> is correct
------------------------------------------------

Next time!
