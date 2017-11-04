\documentclass[sigconf]{acmart}

\usepackage{amsfonts}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{verbatim}
\usepackage{url}
\usepackage{finite-dtypes}

\begin{document}

\title{Finite Dependent Types}
\subtitle{Fancy Types For Systems Metaprogramming}
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
  This work is licensed under a Creative Commons Attribution 4.0 International License.\\
  This paper~\cite{self} is written in Literate Agda, and typechecked with Agda~v2.4.2.5%
}
\setcopyright{none}
\settopmatter{printacmref=false}
\urlstyle{tt}

% Set up the basic definitions.
\begin{comment}
\begin{code}
{-# OPTIONS --type-in-type #-} -- WARNING, CLAXONS!
open import prelude -- POSTULATES LIVE HERE!
\end{code}
\end{comment}

\maketitle

\section{Introduction}

Applications such as web browsers often have issues of scale and
complexity of the code base. For example, the Servo~\cite{servo.org}
next generation web engine contains more than a quarter of a million
lines of code (counted with \texttt{loc}~\cite{loc}):
\begin{tinyverb}
$ loc servo/components/
--------------------------------------------------------------------------------
 Language             Files        Lines        Blank      Comment         Code
--------------------------------------------------------------------------------
 Rust                   811       323350        28930        35208       259212
...
--------------------------------------------------------------------------------
 Total                  961       353834        33406        37472       282956
--------------------------------------------------------------------------------
\end{tinyverb}
That is just the Servo codebase itself. Servo also makes use of the
Cargo~\cite{crates.io} software ecosystem, and has more than two hundred
transitive dependencies with more than a million lines of Rust code,
and nine million lines of code in all languages:
\begin{tinyverb}
$ loc servo/.cargo/
...
 Rust                  2274      1541124        65910       111065      1364149
...
--------------------------------------------------------------------------------
 Total                58295     11784796      1274681      1179475      9330640
--------------------------------------------------------------------------------
\end{tinyverb}
Building Servo generates even more source code:
\begin{tinyverb}
$ loc servo/target/
...
 Rust                   611       893414        74200        13194       806020
...
--------------------------------------------------------------------------------
 Total                 3901      1660507       174703       107729      1378075
--------------------------------------------------------------------------------
\end{tinyverb}
Much of this generated code comes from the \texttt{script} component,
which generates Rust bindings for the Web~IDL~\cite{webidl}
interfaces for the HTML JavaScript APIs~\cite{whatwg}:
\begin{tinyverb}
$ loc servo/target/debug/build/script-*/
...
 Rust                   579       781977        63352         6424       712201
...
--------------------------------------------------------------------------------
 Total                  592       800055        66936         9849       723270
--------------------------------------------------------------------------------
\end{tinyverb}
The code generator itself is twenty thousand lines of Python script:
\begin{tinyverb}
$ loc servo/components/script/dom/bindings/codegen/
...
 Python                  80        26919         3903         2112        20904
...
--------------------------------------------------------------------------------
 Total                   81        26932         3904         2112        20916
--------------------------------------------------------------------------------
\end{tinyverb}
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

% The Agda types of things defined in this figure.
\begin{comment}
\begin{code}
infixr 5 _/times/_ _/rightarrow/_
_/times/_ : ∀ {j k} {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} → (FSet m) -> (FSet n) -> (FSet(m + n))
_/rightarrow/_ : ∀ {j k} {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} → (A : FSet m) -> (FSet n) -> (FSet (n /ll/ m))
\end{code}
\end{comment}

\begin{figure}[t]
\begin{code}
(A /times/ B) = & (/prod/ x /in/ A /cdot/ B) \\
(A /rightarrow/ B) = & (/sum/ x /in/ A /cdot/ B) \\ \\
%nothing =
  /nothing/ &/in/ /FSet/(/zerop/) \\
%unit =
  /unit/ &/in/ /FSet/(/zerop/) \\
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
  /FSet/(n) &/in/ /FSet/(/succp/(n))
\end{code}
\caption{Type rules for built-in types}
\label{built-in-types}
\end{figure}

\subsection{Dependent metaprogramming}

\begin{comment}
\begin{code}
-- We assume 8-bit words in this paper.
/WORDSIZE/ = & [ /false/ , /false/ , /false/ , /true/ , /false/ , /false/ , /false/ , /false/ ] \\
/word/ = & /bits/ (/WORDSIZE/)
-- Not sure what the real cardinality of IO should be
/IO/ : ∀ {k} {n : 𝔹 ↑ k} → FSet(n) → FSet(/WORDSIZE/)
/IO/ = HOLE
-- Pointers
/reference/ : ∀ {k} {n : 𝔹 ↑ k} → FSet(n) → FSet(/WORDSIZE/)
/reference/(A) = record { Carrier = Carrier A ; encodable = HOLE }
-- Strings
/str/ : FSet(/WORDSIZE/)
/str/ = HOLE
-- Console defined below
csize = (/WORDSIZE/ /ll/ /WORDSIZE/) /ll/ /WORDSIZE/
/Console/ : forall /ssize/ -> FSet(/ssize/) -> Carrier(/FSet/(csize))
\end{code}
\end{comment}

Metaprogramming includes the ability to interpret object
languages such as Web~IDL. For example:
\begin{verbatim}
  interface Console { log(DOMString moduleURL); };
\end{verbatim}
might be interpreted as:
\begin{code}
/Console/ = &
  /fn/ /ssize/ /in/ /word/ /cdot/
  /fn/ /DOMString/ /in/ /FSet/(/ssize/) \\&\indent /cdot/
  /prodp/ /csize/ /in/ /word/ /cdot/
  /prodp/ /Console/ /in/ /FSet/(/csize/) \\&\indent /cdot/
  /prodp/ /log/ /in/ /reference/((/Console/ /times/ /DOMString/) /rightarrow/ /IO/(/unit/)) \\&\indent /cdot/
  /unitp/
\end{code}
The important point about this interpretation is that it is internal
to the system, and can be typed. If we define:
\begin{code}
/CSize/ = & (/WORDSIZE/ /ll/ /WORDSIZE/) /ll/ /WORDSIZE/ \\
\end{code}
then the typing of $\kw{Console}$ is internal to the language:
\begin{code}
%Console =
  /Console/(s)(S) &/in/ /FSet/(/CSize/)
  &/WHEN/ S /in/ /FSet/(s)
  /AND/ s /in/ /word/
\end{code}
Chliapala~\cite{Chl10} has shown that dependent metaprogramming
can give type-safe bindings for first-order languages like
SQL schemas. Hopefully it scales to higher-order languages like Web~IDL.
More research is needed!
 
\subsection{Dependent dependencies}

\begin{comment}
\begin{code}
size = [ /false/ , /false/ , /false/ , /false/ , /false/ , /false/ , /false/ , /false/ , /false/ , /false/ , /false/ , /false/ , /true/ ]
/A[1,0]/ : FSet(size)
/A[1,1]/ : FSet(size)
/a[1,0,1]/ : Carrier(/A[1,0]/)
/a[1,0,2]/ : Carrier(/A[1,0]/)
/a[1,1,0]/ : Carrier(/A[1,1]/)
/B[1,0]/ : Carrier(/A[1,1]/) → FSet(size)
/b[1,0,1]/ : ∀ a → (Carrier(/B[1,0]/ a))
\end{code}
\end{comment}

Dependencies are usually versioned, for instance Cargo uses semantic versioning~\cite{semver.org}.
Semantic versions are triples $[x, y, z]$, where the interface for a package only depends on
$[x, y]$, and interfaces with the same $x$ are required to be upwardly compatible.
For example an interface at version [1,0] might consist of a sized type $\kw{T}$
together with an element $\kw{z}\in\kw{T}$:
\begin{code}
/A[1,0]/ = &
  /prodp/ /size/ /in/ /word/ /cdot/
  /prodp/ /T/ /in/ /FSet/(/size/) \\&\indent /cdot/ 
  /prodp/ /z/ /in/ /T/ /cdot/
  /unitp/
\end{code}
One possible implementation sets $\kw{T}$ to be $\kw{unit}$:
\begin{code}
/a[1,0,1]/ = (
  /zerop/ ,
  /unitp/ ,
  /epsilon/ ,
  /epsilon/ )
\end{code}
The next version might set $\kw{T}$ to be $\kw{bool}$:
\begin{code}
/a[1,0,2]/ = (
  /onep/ ,
  /boolp/ ,
  /false/ ,
  /epsilon/ )
\end{code}
Bumping the minor version requires an implementation with a compatible interface.
For example the next major
release might require $\kw{T}$ to support a successor function:
\begin{code}
/A[1,1]/ = &
  /prodp/ /size/ /in/ /word/ /cdot/
  /prodp/ /T/ /in/ /FSet/(/size/) \\&\indent /cdot/ 
  /prodp/ /z/ /in/ /T/ /cdot/
  /prodp/ /s/ /in/ /reference/(/T/ /rightarrow/ /T/) /cdot/
  /unitp/
\end{code}
For instance, this can be implemented by setting $\kw{T}$ to be $\kw{word}$:
\begin{code}
/tsucc/ = & (/fn/ x /cdot/ /truncate/(/one/ + x)) \\
/a[1,1,0]/ = &
  ( /WORDSIZE/
  , /word/
  , /zerop/
  , /tsucc/
  , /epsilon/
  )
\end{code}
Implementations may be dependent, for example $\kw{B}$ might depend on $\kw{A}[1,y]$ for any $y\ge1$:
\begin{code}
/B[1,0]/(/size/ , /A/ , /z/ , /s/ , /ldots/) =
  /prodp/ /ss/ /in/ /reference/(/A/ /rightarrow/ /A/) /cdot/
  /unitp/
\end{code}
with matching implementation:
\begin{code}
/b[1,0,1]/(/size/ , /A/ , /z/ , /s/ , /ldots/) =
  ( (/fn/ x /cdot/ /s/(/s/(x)))
  , /epsilon/
  )
\end{code}
In summary, an interface $A[x,y]$ is interpreted as family of types
where if $y\le y'$ then $A[x,y] :> A[x,y']$ for an appropriate
definition of \emph{interface evolution}.
Dependent packages are treated in the style
of Kripke semantics, as functions
$\forall A[x,y'] <: A[x,y] \cdot B[m,n]$.

There has been much attention paid to dependent types for module
systems~\cite{???}. In some ways, dependency management is simpler
because the dependency graph is required to be acyclic,
but it does introduce interface evolution which can be complex,
for example Rust's~\cite{rfc1105}. More research is needed!

\subsection{Finite dependencies}

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
languages in which finite types are the norm. For example, a simple
language of finite types is given in Figure~\ref{built-in-types}.
This system is not fully developed (\emph{hey, this is a position paper!})
in particular its use of $\kw{FSet}(k) \in \kw{FSet}(k+1)$
is possibly unsound, and its encoding in Agda uses $\kw{Set} \in \kw{Set}$
which is dangerous.

\section{Design space}

There is a large design space for finite dependent types, and types for systems programs.

\subsection{Type of types}

What should the size of $\kw{FSet}$ be?
In Figure~\ref{built-in-types} the type is $\kw{FSet}(n) \in \kw{FSet}(\kw{one} + n)$
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

In the theory in Figure~\ref{built-in-types}, there is an implicit isomorphism
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

Dependent types are a good fit for some of the more difficult problems
with programming in the large: metaprogramming and dependency management.
Howeever, their focus on infinite types such as $\mathbb{N}$ is a mismatch.
Systems are finite, and are better served by systems which
encourage the use of finite types.

\sloppy
\bibliographystyle{plain}
\bibliography{finite-dtypes}

\end{document}

