\documentclass[sigconf]{acmart}

\usepackage{amsfonts}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{verbatim}
\usepackage{url}
\usepackage{finite-dtypes}

\begin{document}

\title{Finite Dependent Types}
\subtitle{Fancy Types For Systems Programs}
\author{Alan Jeffrey}
\orcid{0000-0001-6342-0318}
\affiliation{Mozilla Research}
\email{ajeffrey@mozilla.com}
\acmConference{Submitted for publication}{November 2017}{}
\acmDOI{}
\acmISBN{}
\acmYear{2018}
\copyrightyear{%
  \includegraphics[height=1.5ex]{cc-by-88x31.png}
  \url{https://creativecommons.org/licenses/by/4.0/}\\
  This work is licensed under a Creative Commons Attribution 4.0 International License%
}
\setcopyright{none}
\settopmatter{printacmref=false}
\urlstyle{tt}

\maketitle

\section{Introduction}

Applications such as web browsers often have issues of scale
and complexity of the code base. For example, the next-generation
Servo~\cite{servo.org} web engine contains more than a quarter of a
million lines of code (counted with \texttt{loc}~\cite{loc}):
\begin{verbatim}
$ loc servo/components/
--------------------------------------------------------------------------------
 Language             Files        Lines        Blank      Comment         Code
--------------------------------------------------------------------------------
 Rust                   811       323350        28930        35208       259212
...
--------------------------------------------------------------------------------
 Total                  961       353834        33406        37472       282956
--------------------------------------------------------------------------------
\end{verbatim}
That is just the Servo codebase itself. Servo also makes use of the
Cargo~\cite{crates.io}
software ecosystem, and has more than 200 transitive dependencies with
more than a million lines of Rust code, and nine million lines of code
in all languages:
\begin{verbatim}
$ loc servo/.cargo/
...
 Rust                  2274      1541124        65910       111065      1364149
...
--------------------------------------------------------------------------------
 Total                58295     11784796      1274681      1179475      9330640
--------------------------------------------------------------------------------
\end{verbatim}
Building Servo generates even more source code:
\begin{verbatim}
$ loc servo/target/
...
 Rust                   611       893414        74200        13194       806020
...
--------------------------------------------------------------------------------
 Total                 3901      1660507       174703       107729      1378075
--------------------------------------------------------------------------------
\end{verbatim}
Much of this generated code comes from the \texttt{script} component,
which generates Rust bindings for the WebIDL~\cite{webidl}
interfaces for the HTML JavaScript APIs~\cite{whatwg}.
\begin{verbatim}
$ loc servo/target/debug/build/script-*/
...
 Rust                   579       781977        63352         6424       712201
...
--------------------------------------------------------------------------------
 Total                  592       800055        66936         9849       723270
--------------------------------------------------------------------------------
\end{verbatim}
The code generator itself is twenty thousand lines of Python script:
\begin{verbatim}
$ loc servo/components/script/dom/bindings/codegen/
...
 Python                  80        26919         3903         2112        20904
...
--------------------------------------------------------------------------------
 Total                   81        26932         3904         2112        20916
--------------------------------------------------------------------------------
\end{verbatim}
There should be a better way to do metaprogramming than Python scripts
writing source files!

\section{Metaprogramming}

Fortunately, metaprogramming is a well-explored area, 
notably in the Racket~\cite{racket-lang.org} programming
language's \texttt{\#lang} declarations.
Much metaprogramming does not provide static guarantees,
since the type system of the metaprogramming language
is not usually expressive enough to encode object
language types, especially when those types are based on
data (such as Web IDL specifications).

A notable exception is the use of \emph{dependent types}
(as implemented in, for example, Coq~\cite{coq}, Agda~\cite{agda}
or Idris~\cite{idris}). Dependent types have already been proposed
for low-level programming~\cite{CHAGN07}, generic programming~\cite{AM03}
and metaprogramming~\cite{Chl10}. Dependent types allow for
the compile-time computation of types which depend on data,
but still provide static guarantees such as memory safety.

\subsection{Dependent metaprogramming}

In order for a system to allow type-safe metaprogramming, it should be
able to parse and interpret object languages. Such languages include
ASTs for surface syntax, the intermediate language (parameterized by
type) and machine code (parameterized by architecture).

A desugaring function for top-level programs would have type $\kw{AST}
\rightarrow \kw{F}(\kw{IL}(\kw{prog}))$, for an appropriate monad
$\kw{F}$ to account for failure, and type $\kw{prog}$ for executable
programs. Such a function can account for features such as Haskell
$\kw{do}$-notation, or Rust macros and $\#\kw{derive}$ declarations.

A compiler to architecture $x$ would have type
$\kw{IL}(\kw{prog}) \rightarrow \kw{MC}(x)$. An exec
function for the current architecture $\kw{ARCH}$ would have type
$\kw{MC}(\kw{ARCH}) \rightarrow \kw{IO}(\kw{unit})$. Given those
it's possible, for example, to implement a
JIT compiler with type $\kw{IL}(\kw{prog}) \rightarrow
\kw{IO}(\kw{unit})$.

Building software often includes complex
I/O effects, such as downloading dependencies, and interacting with
the file system. The type of a program which downloads dependencies,
then compiles a program is $\kw{IO}(\kw{F}(\kw{MC}(x)))$. Note that this
type supports staged computation, which makes it easier to ensure
build repeatability.

\subsection{Dependent dependencies}

Dependencies are usually versioned, for example by semantic versioning~\cite{semver}.
Semantic versions are triples $(x, y, z)$ where the API for a package only depends on
$(x, y)$, but its implementation may depend on $(x, y, z)$. Moreover, APIs
with the same $x$ are meant to be upwardly compatible.

For example an interface $A(1,0)$ might be:
\[
  \{ \kw{size} \in \kw{word}
  , \kw{A} : \kw{FSet}(\kw{size})
  , \kw{z} : \kw{A}
  \}
\]
with implementation $a(1,0,1)$:
\[
  [ \kw{0}
  , \kw{unit}
  , \kw{()}
  ]
\]
When $a(1,0,1)$ is released, its interface is still $A(1,0)$ but its implementation is allowed to change:
\[
  [ \kw{1}
  , \kw{bool}
  , \kw{false}
  ]
\]
$A(1,1)$ is required to have a compatible interface, for simplicity we will take this
to be an extension:
\[
  \{ \kw{size} : \kw{word}
  , \kw{A} : \kw{FSet}(\kw{size})
  , \kw{z} : \kw{A}
  , \kw{s} : \kw{A} \rightarrow \kw{A}
  \}
\]
for example $a(1,1,1)$ might be:
\[
  [ \kw{WORDSIZE}
  , \kw{word}
  , \kw{0}
  , \lambda x \cdot \kw{truncate}(\kw{1} + x)
  ]
\]
Implementations may be dependent, for example $B(1,1)$ might depend on $A(1,y)$ for any $y\ge1$:
\[
  \{ \kw{size} : \kw{word}
  , \kw{A} : \kw{FSet}(\kw{size})
  , \kw{z} : \kw{A}
  , \kw{s} : \kw{A} \rightarrow \kw{A}
  , \cdots
  \}
  \rightarrow
  \{ \kw{one} : \kw{A}
  \}
\]
with matching implementation:
\[
  \lambda
  [ \kw{size}
  , \kw{A}
  , \kw{z}
  , \kw{s}
  , \cdots
  ]
  \cdot
  [ s(z)
  ]
\]
In summary, an interface $A(x,y)$ is interpreted as family of types
where $A(x,1+y)$ is an extension of $A(x)$, and
implementation is interpreted as a family of values
where $a(x, y, z) \in A(x, y)$.
A dependent interface (resp.~implementation) is interpreted as
a dependent function type (resp.~dependent function).

\subsubsection{Finite dependencies}

One feature that all of these examples have in common is that they do not
require any infinite data. Existing dependent type systems encourage the
use of infinite types such such as lists or trees.
The prototypical infinite types are $\mathbb{N}$ (the type of natural
numbers) and $\kw{Set}$ (the type of types). This is a mismatch with systems
programs, where types are often \emph{sized} (for example in Rust,
types are \texttt{Sized}~\cite[\S3.31]{rust-book} by default).
In particular, systems programs are usually parameterized by the
architectures word size, and assume that data fits into memory
(for example that arrays are indexed by a word, not by a natural number).

In this position paper, we encourage the exploration of programming
languages in which finite types are the norm. In \S\ref{hacking} we
present a simple system for finite types, where $\kw{bits}(k)$
replaces $\mathbb{N}$ and $\kw{FSet}(k)$ replaces $\kw{Set}$.
In each case $k$ is the bitlength of the type, for example
if we define $\kw{two} = [\kw{0},\kw{1}]$
and $\kw{three} = [\kw{1},\kw{1}]$
then $\kw{two} \in \kw{bits}(\kw{two}) \in \kw{FSet}(\kw{two}) \in \kw{FSet}(\kw{three})$.

This system is not fully developed (\emph{hey, this is a position paper!})
in particular its use of $\kw{FSet}(k) \in \kw{FSet}(k+1)$
is possibly unsound, and its encoding in Agda uses $\kw{Set} \in \kw{Set}$
which is dangerous. \S\ref{hacking} is written in Literate Agda, and has
been typechecked with Agda~v2.4.2.5. The source is available~\cite{self}.

\section{Simple finite dependent types}
\label{hacking}

% Set up the basic definitions.
\begin{comment}
\begin{code}
{-# OPTIONS --type-in-type #-} -- WARNING, CLAXONS!
open import prelude -- POSTULATES LIVE HERE!
\end{code}
\end{comment}

% The Agda types of things defined in this section.
\begin{comment}
\begin{code}
infixr 5 _/times/_ _/rightarrow/_ _/oplus/_
_/times/_ : ∀ {j k} {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} → (FSet m) -> (FSet n) -> (FSet(m + n))
_/rightarrow/_ : ∀ {j k} {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} → (A : FSet m) -> (FSet n) -> (FSet (n /ll/ m))
_/oplus/_ : ∀ {k} {m : 𝔹 ↑ k} → (FSet m) → (FSet m) → (FSet (/one/ + m))
/inl/ : ∀ {k} → {n : 𝔹 ↑ k} → {A B : FSet(n)} → Carrier(/sum/ x /in/ A /cdot/ (A /oplus/ B))
/inr/ : ∀ {k} → {n : 𝔹 ↑ k} → {A B : FSet(n)} → Carrier(/sum/ y /in/ B /cdot/ (A /oplus/ B))
_/?/ : ∀ {k} {m : 𝔹 ↑ k} → (FSet m) → (FSet (/one/ + m))
/some/ : ∀ {k} → {n : 𝔹 ↑ k} → {A : FSet(n)} → Carrier(/sum/ x /in/ A /cdot/ (A /?/))
/none/ : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → Carrier(A /?/)
\end{code}
\end{comment}

\begin{figure}[t]
\begin{code}
(A /times/ B) = & (/prod/ x /in/ A /cdot/ B) \\
(A /rightarrow/ B) = & (/sum/ x /in/ A /cdot/ B) \\ \\
%nothing =
  /nothing/ &/in/ /FSet/(/zero/) \\
%unit =
  /unit/ &/in/ /FSet/(/zero/) \\
%bool =
  /bool/ &/in/ /FSet/(/one/) \\
%prod = \ j k (m : 𝔹 ↑ j) (n : 𝔹 ↑ k) ->
  (/prod/ x /in/ A /cdot/ B(x)) &/in/ /FSet/(m + n) \\
  &/WHEN/ B /in/ (A /rightarrow/ /FSet/(n))
  /AND/ A /in/ /FSet/(m) \\
%sum = \ j k (m : 𝔹 ↑ j) (n : 𝔹 ↑ k) ->
  (/sum/ x /in/ A /cdot/ B(x)) &/in/ /FSet/ (n /ll/ m) \\
  &/WHEN/ B /in/ (A /rightarrow/ /FSet/(n))
  /AND/ A /in/ /FSet/(m) \\
%FSet = \ k (n : 𝔹 ↑ k) ->
  /FSet/(n) &/in/ /FSet/(/one/ + n)
\end{code}
\caption{Type rules for built-in types}
\label{built-in-types}
\end{figure}

In this presentation of finite dependent types, we take binary
arithmetic (with constants, addition and shifting) as a primitive,
encoded little-endian. There is a type $\kw{bits}(k)$ for
bitstrings of length $k$. For example, we can go old-school and
assume a word size of eight bits:
\begin{code}
/WORDSIZE/ = & [ /0/ , /0/ , /0/ , /1/ , /0/ , /0/ , /0/ , /0/ ] \\
/word/ = & /bits/ (/WORDSIZE/)
\end{code}
This is spookily cyclic:
\begin{code}
%WORDSIZE =
  /WORDSIZE/ &/in/ /word/ \\
%word =
  /word/ &/in/ /FSet/(/WORDSIZE/)
\end{code}
We can break this cycle by expanding out the definition of $\kw{bits}$:
\begin{code}
%WORDSIZE-expanded =
  /WORDSIZE/ &/in/ (/bool/ /times/ /bool/ /times/ /bool/ /times/ /bool/ \\&\indent
                      /times/ /bool/ /times/ /bool/ /times/ /bool/ /times/ /bool/ /times/ /unit/) \\
             &/in/ (/FSet/ ([ /0/ , /0/ , /0/ , /1/ ])) \\
%four =
  ([ /0/ , /0/ , /0/ , /1/ ]) &/in/ (/bool/ /times/ /bool/ /times/ /bool/ /times/ /bool/ /times/ /unit/) \\
             &/in/ /FSet/ ([ /0/ , /0/ , /1/ ]) \\           
%three =
  ([ /0/ , /0/ , /1/ ]) &/in/ (/bool/ /times/ /bool/ /times/ /bool/ /times/ /unit/) \\
             &/in/ /FSet/ ([ /1/ , /1/ ]) \\           
%two =
  ([ /0/ , /1/ ]) &/in/ (/bool/ /times/ /bool/ /times/ /unit/) \\
             &/in/ /FSet/ ([ /0/ , /1/ ])
\end{code}
The $\kw{bits}$ type is not primitive, since it can be defined
by induction:
\begin{code}
/mybits/ = /indn/(/FSet/) (/unitp/) (/lambda/ n /cdot/ /lambda/ A /cdot/ (/bool/ /times/ A))
\end{code}
For example:
\begin{code}
%WORDSIZE-mybits =
  /WORDSIZE/ &/in/ /mybits/(/WORDSIZE/)
\end{code}
At this point, we have seen all of the gadgets in this simple finite
dependent type system. The types are summarized in
Figure~\ref{built-in-types}.

\section{Design space}

There is a large design space for finite dependent types, and types for systems programs.

\subsection{Type of types}

What should the size of $\kw{FSet}$ be?
In \S\ref{hacking} the type is $\kw{FSet}(n) \in \kw{FSet}(\kw{one} + n)$
which models a theory in which types are identified with their cardinality,
since the cardinality of $\{ 0,\ldots,n \}$ is $n+1$, and if $n$ is a $k$-bit number
then $n+1$ is a $k$-bit number.

There are alternatives, such as to identify a type with the set of
bitstrings they contain, so each element of $\kw{FSet}(n)$ is a subset of
$2^n$, so $\kw{FSet}(n)$ can be represented in $2^n$ bits, which would
give $\kw{FSet}(n) \in \kw{FSet}(\kw{one} \ll n)$. Alternatively, we
could postulate an uninterpreted increasing function $f$ and set
$\kw{FSet}(n) \in \kw{FSet}(f(n))$.

Alternatives which would be problematic is to consider types to be irrelevant,
and so $\kw{FSet}(n) \in \kw{FSet}(\kw{zero})$, or to be considered just to be identified
with their inhabitance, and so $\kw{FSet}(n) \in \kw{FSet}(\kw{one})$. In either case,
we have $\kw{FSet}(n) \in \kw{FSet}(n)$ for some $n$, which would be unsound.

\subsection{Path types}

Dependent type systems usually come with an identity type $a \equiv_A b$
where $a : A$ and $b : A$. Finite types are no different, but we get a choice
for what to use as the bitlength, which raises similar questions as for the
type of types.

If identity types are interpreted as paths as in Homotopy Type Theory~\cite{hott},
then the size of $A \equiv_{\kw{FSet}(n)} B$ is at most the size of $A \rightarrow B$,
which would suggest considering $(a \equiv_A b) \in \kw{FSet}(n \ll n)$
when $A \in \kw{FSet}(n)$.

This makes the type of identities over $A$ different from the type of $A$,
since $\kw{FSet}(n \ll n)$ is much larger than $\kw{FSet}(n)$. This may give problems
with, for example, codings of GADTs.

\subsection{Irrelevance}

In any dependent type system, questions of how to model
irrelevant~\cite{???} data quickly arise, for example Agda's $.A$
type, where for any $a,b \in .A$ we have $a \equiv_{.A}
b$. Irrelevance particularly affects finite types, since the size of
an irrelevant set is at most one, so we would expect it to have type
$\kw{FSet}(\kw{zero})$, but this means that $.\kw{FSet}(n) \in
\kw{FSet}(n)$ which is skirting very close to unsoundness.

One place where irrelevance would be very useful is in bitlengths of
bitlengths, which should not matter: $\kw{FSet}([\kw{1}])$ should be
the same as $\kw{FSet}([\kw{1},\kw{0}])$.

\subsection{Serialization}

In the theory in \S\ref{hacking}, there is an implicit isomorphism
between elements of $\kw{FSet}(n)$ and subsets of $\kw{bool}^n$. The isomorphism defines
a (de)serializer, for example serializing pairs by serializing each projection,
and serializing functions by serializing the graph of the function.

Part of the design space of a finite type system is how explicit this
isomorphsim should be. Options include including it in the metatheory,
including it as irrelevant data in the theory, and including it as
relevant data in the theory.

The last choice means that every type comes equipped with a serializer,
which in turn means that parametricity~\cite{parametricity} does not
hold, and so there are no theorems for free~cite{tff} any more.

\subsection{Induction}

In the theory in \S\ref{hacking}, induction over binary
numbers is taken as a primitive. It would be nice if this could be
encoded by induction over the booleans and dependent pairs,
with induction over numbers relegated to the metatheory.

\subsection{Theory of binary arithmetic}

The theory of finite types is very dependent on the theory of natural
numbers, and it is very easy to end up type checking dependant on
properties such as associativity and commutativity of addition.
Such theorems could be handled by an SMT solver, but this has its own
issues, such as the interaction between the SMT solver and type
inference, and the complexity of an SMT solver being visible to
the end programmer.

\subsection{Pointers}

In systems programming languages such as Rust, cyclic data structures
are mediated by pointers. In a finite type system, we could allow a
type of pointers $\&(A)$ where $\&(A) \in \kw{FSet}(\kw{WORDSIZE})$
when $A \in \kw{FSet}(n)$.
A typical example is the AST type for a language, which will be a
type $\kw{AST}$ containing pointers of type $\&\kw{AST}$.

Pointer creation can fail in low-memory situations, so should be
encapsulated in a monad, for example the parser for an AST would have
type $\&\kw{str} \rightarrow \kw{F}(\kw{AST})$ for an appropriate monad $\kw{F}$
which includes failure.

Care needs to be taken about pointers to data which includes sets,
in particular $\&(\kw{FSet}(\kw{WORDSIZE})) \in
\kw{FSet}(\kw{WORDSIZE})$ is very close to introducing unsoundness.

\section{Conclusions}

Systems are finite, and are better served by systems which
encourage the use of finite types.

\sloppy
\bibliographystyle{plain}
\bibliography{finite-dtypes}

\end{document}




The definition of tagged union in terms of dependent pairs:
\begin{code}
(A /oplus/ B) = & (/prod/ b /in/ /bool/ /cdot/ /IF/ b /THEN/ A /ELSE/ B) \\
/inl/(x) = & (/1/ , x) \\
/inr/(y) = & (/0/ , y)
\end{code}
The definition of options in terms of tagged unions:
\begin{code}
(A /?/) = & (A /oplus/ /bits/(/sizeof/(A))) \\
/some/(x) = & /inl/(x) \\
/none/(A) = & /inr/(/zero/[ /sizeof/(A) ])
\end{code}
Derived typing rules:
\begin{code}
%times = \ k (m n : 𝔹 ↑ k) ->
  (A /times/ B) &/in/ /FSet/(m + n)
  &/WHEN/ A /in/ /FSet/(m)
  /AND/ B /in/ /FSet/(n) \\
%rightarrow = \ j k (m : 𝔹 ↑ j) (n : 𝔹 ↑ k) ->
  (A /rightarrow/ B) &/in/ /FSet/(n /ll/ m)
  &/WHEN/ A /in/ /FSet/(m)
  /AND/ B /in/ /FSet/(n) \\
%oplus = \ k (n : 𝔹 ↑ k) ->
  (A /oplus/ B) &/in/ /FSet/(/one/ + n)
  &/WHEN/ A /in/ /FSet/(n)
  /AND/ B /in/ /FSet/(n) \\
%? = \ k (n : 𝔹 ↑ k) ->
  (A /?/) &/in/ /FSet/(/one/ + n)
  &/WHEN/ A /in/ /FSet/(n)
\end{code}
