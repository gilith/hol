The hol package
===============

The [hol package][] is a [Haskell][] library that implements a higher order logic kernel. It can read proof files in [OpenTheory][] format, and includes a pretty-printer compatible with the [standard theory library][].

This software is released under the [MIT License][].

Install
-------

Installing the hol package requires [cabal][]:

    git clone https://github.com/gilith/hol.git
    cd hol
    cabal install

Test
----

Use [cabal][] to run the test suite:

    cabal test

Run
----

The hol package contains an executable called hol-pkg, which is run as follows:

    Usage: hol-pkg INPUT
    where INPUT is one of the following forms:
      FILE.art     : a proof article file
      FILE.thy     : a theory package file
      NAME-VERSION : a specific version of an installed theory package
      NAME ...     : the latest installed version of a list of packages

The hol-pkg program reads the INPUT to generate a set of theorems, which are pretty-printed to standard output together with the symbols they contain. For example,

    hol-pkg unit

reads the latest installed version of the unit theory package to generate a set of 5 theorems, resulting in the following output:

    3 type operators: (->) bool unit
    6 constants: (=) (!) (==>) (?) (?!) ()
    5 theorems:
      |- !v. v = ()
      |- !f g. f = g
      |- !e. ?fn. fn () = e
      |- !e. ?!fn. fn () = e
      |- !p. p () ==> !x. p x

Profile
-------

Before starting, make sure the GHC system and the GHC text, transformers and parsec libraries are installed with profiling support. On a Debian system the following command installs them:

     apt-get install ghc-prof libghc-text-prof libghc-transformers-prof libghc-parsec3-prof

Next use [cabal][] to install the other dependent libraries with profiling support:

    cabal sandbox init
    cabal configure --enable-library-profiling --enable-profiling --enable-benchmarks
    cabal install --only-dependencies --enable-library-profiling

Build the hol package library and benchmark program:

    cabal configure --enable-library-profiling --enable-profiling --enable-benchmarks
    cabal build

Use the [opentheory tool] to create a benchmark file:

     opentheory info --article -o base.art base

Then use [cabal][] to run the benchmark:

    cabal bench

The time and memory allocation profile of the program can be viewed in text format:

    less hol-profile.prof

Alternatively the memory allocation profile can be viewed as a graph:

    hp2ps -e8in -c hol-profile.hp
    ps2pdf hol-profile.ps
    xpdf hol-profile.pdf

[cabal]: https://www.haskell.org/cabal/ "Cabal"
[Haskell]: https://www.haskell.org/
[hol package]: https://hackage.haskell.org/package/hol "hol package"
[MIT License]: https://github.com/gilith/hol/blob/master/LICENSE "MIT License"
[OpenTheory]: http://www.gilith.com/research/opentheory/ "The OpenTheory project home page"
[opentheory tool]: http://www.gilith.com/software/opentheory/ "The opentheory tool"
[standard theory library]: http://opentheory.gilith.com/?pkg=base "The OpenTheory standard theory library"
