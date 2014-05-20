---
layout: post
title: Hello VST, hello Verifiable C
---

<center><h1 style="color: red; background-color: yellow;">draft draft draft draft draft</h1></center>

On today's show:

* Table of Contents
{:toc}

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

At time of writing, the latest release of VST is Version 1.3, which is compatible with CompCert 2.1 (which is not the latest CompCert).

Download link for CompCert 2.1: [http://compcert.inria.fr/release/compcert-2.1.tgz](http://compcert.inria.fr/release/compcert-2.1.tgz), or, if that's stale, you can get a copy from me: [http://intoverflow.github.io/assets/compcert-2.1.tgz](http://intoverflow.github.io/assets/compcert-2.1.tgz).

Download link for VST 1.3: [http://vst.cs.princeton.edu/download/vst-1.3.tgz](http://vst.cs.princeton.edu/download/vst-1.3.tgz), or, if that's stale, you can get a copy from me: [http://intoverflow.github.io/assets/vst-1.3.tgz](http://intoverflow.github.io/assets/vst-1.3.tgz).

<div style="background-color: #D6EBFF;">
<pre>
<i>[tcarstens@weibel ~]$</i> <b>mkdir verifiable-c</b>
<i>[tcarstens@weibel ~]$</i> <b>cd verifiable-c/</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>wget --quiet "http://compcert.inria.fr/release/compcert-2.1.tgz"</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>wget --quiet "http://vst.cs.princeton.edu/download/vst-1.3.tgz"</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>md5sum *</b>
4581f9756bef08da363d954e7ad20e84  compcert-2.1.tgz
895cd400c9f6d59b8f104a42d7bf4c98  vst-1.3.tgz
<i>[tcarstens@weibel verifiable-c]$</i> <b>sha256sum *</b>
bcb507d998a956c96672bd0f88a2bd792f08f564985675748902420b068862eb  compcert-2.1.tgz
5dbe2f9aeb200959850c52bed14ce533f9ed548a9fbcbd7f8644813d5c56bc43  vst-1.3.tgz
<i>[tcarstens@weibel verifiable-c]$</i>
</pre>
</div>

So far so good. Now we inspect our host for dependencies. In my case, I'm running Linux x86-64, with the intent to have CompCert target arm-eabi. You'll note that I therefore have two gcc's installed; when building CompCert, I'll need to specify which gcc to use.

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

Very good, let's build CompCert, noting my <code><b>toolprefix</b></code> setting (if I wanted to use gcc and not arm-none-eabi-gcc, I would have omitted the toolprefix switch):

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel verifiable-c]$</i> <b>tar -xf compcert-2.1.tgz </b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>pushd compcert-2.1</b>
~/verifiable-c/compcert-2.1 ~/verifiable-c
<i>[tcarstens@weibel compcert-2.1]$</i> <b>./configure arm-eabi -toolprefix arm-none-eabi-</b>
Testing assembler support for CFI directives... no

CompCert configuration:
    Target architecture........... arm
    Application binary interface.. eabi
    OS and development env........ linux
    C compiler.................... arm-none-eabi-gcc
    C preprocessor................ arm-none-eabi-gcc -U__GNUC__ '-D__REDIRECT(name,proto,alias)=name proto' '-D__REDIRECT_NTH(name,proto,alias)=name proto' -E
    Assembler..................... arm-none-eabi-gcc -c
    Assembler supports CFI........ false
    Assembler for runtime lib..... arm-none-eabi-gcc -c
    Linker........................ arm-none-eabi-gcc
    Math library.................. -lm
    Binaries installed in......... /usr/local/bin
    Runtime library provided...... true
    Library files installed in.... /usr/local/lib/compcert
    cchecklink tool supported..... false

If anything above looks wrong, please edit file ./Makefile.config to correct.

<i>[tcarstens@weibel compcert-2.1]$</i> <b>time make -j 6 clightgen</b>
COQC lib/Coqlib.v
COQC lib/Axioms.v
COQC flocq/Core/Fcore_Zaux.v
<i>...(output elided)...</i>
ocamlbuild -j 2 -no-hygiene -no-links -I lib -I common -I arm/eabi -I arm -I backend -I cfrontend -I driver -I flocq/Core -I flocq/Prop -I flocq/Calc -I flocq/Appli -I exportclight -I extraction -I cparser -I exportclight Clightgen.native \
        &amp;&amp; rm -f clightgen &amp;&amp; ln -s _build/exportclight/Clightgen.native clightgen
Finished, 1 target (0 cached) in 00:00:00.
+ /usr/bin/ocamlyacc cparser/Parser.mly
2 shift/reduce conflicts.
Finished, 377 targets (0 cached) in 00:00:05.

real	10m9.582s
user	26m55.107s
sys	0m34.790s
<i>[tcarstens@weibel compcert-2.1]$</i> <b>./clightgen --help</b>
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
<i>[tcarstens@weibel compcert-2.1]$</i> <b>popd</b>
~/verifiable-c
<i>[tcarstens@weibel verifiable-c]$</i>
</pre>
</div>

Sweet. Now we can build VST:

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel verifiable-c]$</i> <b>tar -xf vst-1.3.tgz</b>
<i>[tcarstens@weibel verifiable-c]$</i> <b>pushd vst</b>
~/verifiable-c/vst ~/verifiable-c
<i>[tcarstens@weibel vst]$</i> <b>echo "COMPCERT=../compcert-2.1" > CONFIGURE</b>
<i>[tcarstens@weibel vst]$</i> <b>cat CONFIGURE</b>
COMPCERT=../compcert-2.1
<i>[tcarstens@weibel vst]$</i> <b>time make -j 6</b>
Makefile:275: .depend: No such file or directory
coqdep -slash  -I msl -as msl  -I sepcomp -as sepcomp  -I veric -as veric  -I floyd -as floyd  -I progs -as progs    -R ../compcert-2.1 -as compcert msl/Axioms.v msl/Extensionality.v msl/base.v msl/eq_dec.v <i>(output elided)</i>  > .depend
echo  -I msl -as msl  -I sepcomp -as sepcomp  -I veric -as veric  -I floyd -as floyd  -I progs -as progs    -R ../compcert-2.1 -as compcert >.loadpath
<i>...(output elided)...</i>
COQC progs/verif_insertion_sort.v
&lt;W> Grammar extension: in [constr:operconstr] some rule has been masked
&lt;W> Grammar extension: in [constr:operconstr] some rule has been masked
&lt;W> Grammar extension: in [constr:operconstr] some rule has been masked
&lt;W> Grammar extension: in [constr:pattern] some rule has been masked

real	30m2.202s
user	73m38.990s
sys	0m35.403s
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
~/verifiable-c ~/verifiable-c
<i>[tcarstens@weibel verifiable-c]$</i>
</pre>
</div>

Excellent. As you can see, we've made it to a point where we can work with the VST sample programs (in the case above, <code>sumarray</code>).

Now let's write and verify something of our own.


<code>strncat</code> in Verifiable C
===================================

Here is a simple <code>strncat</code> implementation, along with its representation as CompCert Clight abstract syntax in Coq (download links for [<code>strncat.c</code>](/assets/strncat/strncat.c) and [<code>strncat.v</code>](/assets/strncat/strncat.v)):

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel strncat]$</i> <b>cat strncat.c</b>
typedef unsigned int size_t;

size_t strlen(const char *s) {
  size_t i;
  char c;

  i = 0;
  c = s[i];
  while ('\0' != c) {
    i++;
    c = s[i];
  }

  return i;
}

char *strncat(char *dest, const char *src, size_t n) {
  size_t dest_len = strlen(dest);
  size_t i;

  for (i = 0; i < n && src[i] != 0; i++)
    dest[dest_len + i] = src[i];
  dest[dest_len + i] = 0;

  return dest;
}


<i>[tcarstens@weibel strncat]$</i> <b>~/verifiable-c/compcert-2.1/clightgen strncat.c</b>
<i>[tcarstens@weibel strncat]$</i> <b>cat strncat.v</b>
Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _dest : ident := 8%positive.
Definition _i : ident := 5%positive.
Definition _strncat : ident := 12%positive.
Definition _n : ident := 10%positive.
Definition ___builtin_annot_intval : ident := 3%positive.
Definition ___builtin_memcpy_aligned : ident := 2%positive.
Definition ___builtin_fabs : ident := 1%positive.
Definition _c : ident := 6%positive.
Definition _dest_len : ident := 11%positive.
Definition _s : ident := 4%positive.
Definition _strlen : ident := 7%positive.
Definition _src : ident := 9%positive.
Definition _main : ident := 13%positive.
Definition _dest_len' : ident := 14%positive.


Definition f_strlen := {|
  fn_return := tuint;
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
  fn_params := ((_dest, (tptr tuchar)) :: (_src, (tptr tuchar)) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_dest_len, tuint) :: (_i, tuint) :: (15%positive, tint) ::
               (_dest_len', tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _dest_len')
      (Evar _strlen (Tfunction (Tcons (tptr tuchar) Tnil) tuint))
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
                (Sset 15%positive
                  (Ecast
                    (Ebinop One
                      (Ederef
                        (Ebinop Oadd (Etempvar _src (tptr tuchar))
                          (Etempvar _i tuint) (tptr tuchar)) tuchar)
                      (Econst_int (Int.repr 0) tint) tint) tbool))
                (Sset 15%positive (Ecast (Etempvar 15%positive tbool) tint)))
              (Sset 15%positive (Econst_int (Int.repr 0) tint)))
            (Sifthenelse (Etempvar 15%positive tint) Sskip Sbreak))
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
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)))
     (Tcons tdouble Tnil) tdouble)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid)) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint)))
     (Tcons (tptr tuchar) (Tcons tint Tnil)) tint)) ::
 (_strlen, Gfun(Internal f_strlen)) ::
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

Let's launch CoqIDE. First we need to set up some load paths, so that we can open up the CompCert and VST libraries. Then we're good to go:

<div style="background-color: #D6EBFF;">
<pre style="white-space: pre-wrap;">
<i>[tcarstens@weibel strncat]$</i> <b>ln -s ~/verifiable-c/compcert-2.1 compcert</b>
<i>[tcarstens@weibel strncat]$</i> <b>ln -s ~/verifiable-c/vst vst</b>
<i>[tcarstens@weibel strncat]$</i> <b>cat .loadpath</b>
-I vst/msl -as msl -I vst/sepcomp -as sepcomp -I vst/veric -as veric -I vst/floyd -as floyd -I vst/progs -as progs -R compcert -as compcert
<i>[tcarstens@weibel strncat]$</i> <b>coqc `cat .loadpath` strncat.v</b>
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
          SEP (`(array_at tuchar sh contents 0 size) (eval_id _s))
  POST [ tuint ]
        local (`(eq (Vint (Int.repr len))) retval)
              && `(array_at tuchar sh contents 0 size s0).

</pre>
</div>

This specification says that <code>strlen</code> takes an argument <code>_s</code> which is an array of <code>char</code>s of size <code>size</code>. It posits that this array is a null-terminated ascii string of length <code>len</code>, in the sense described above (see our <code>ascii_string</code> definition).

It says that <code>strlen</code> returns a machine <code>int</code> which is equivalent to <code>len</code> (modulo <code>8*sizeof(int)</code>).

Lastly, it says that <code>strlen</code> does not modify the data pointed-to by <code>_s</code>.

A formal proof that our <code>strncat</code> is correct
------------------------------------------------


First we bundle up all of our definitions and specifications:

<div style="background-color: #FFFFDB;">
<pre>
Definition Vprog : varspecs := nil.
Definition Gprog : funspecs :=  strlen_spec :: nil.
Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

</pre>
</div>

Now we can state and prove a lemma about <code>strlen</code> meeting its specification:

<div style="background-color: #FFFFDB;">
<pre>
Lemma body_strlen: semax_body Vprog Gtot f_strlen strlen_spec.
</pre>
</div>


