\documentclass[sigconf]{acmart}

\usepackage{amsfonts}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{verbatim}
\usepackage{url}
\usepackage{finite-dtypes}

\begin{document}

\title{Finite Dependent Types}
\subtitle{Fancy Types For Systems Metaprogramming And Dependency Management}
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
next generation web engine contains more than 250KLoC:
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
Cargo~\cite{crates.io} software ecosystem, and has over 200
transitive dependencies with more than a 1MLoC in Rust,
and 9MLoC in total:
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
which generates Rust bindings from Web~IDL~\cite{webidl}:
\begin{tinyverb}
$ loc servo/target/debug/build/script-*/
...
 Rust                   579       781977        63352         6424       712201
...
--------------------------------------------------------------------------------
 Total                  592       800055        66936         9849       723270
--------------------------------------------------------------------------------
\end{tinyverb}
The code generator itself is 20KLoC in Python:
\begin{tinyverb}
$ loc servo/components/script/dom/bindings/codegen/
...
 Python                  80        26919         3903         2112        20904
...
--------------------------------------------------------------------------------
 Total                   81        26932         3904         2112        20916
--------------------------------------------------------------------------------
\end{tinyverb}
Is there a more principled approach to code generation?

\section{Metaprogramming}

Fortunately, metaprogramming is a well-explored area, 
notably in the Racket~\cite{racket-lang.org} programming
language's \texttt{\#lang} ecosystem.
Much metaprogramming relies on dynamic checks,
since the host language's type system
is not usually expressive enough to encode object
language types at compile time.

A notable exception is the use of \emph{dependent types}
(as implemented in, for example, Coq~\cite{coq}, Agda~\cite{agda}
or Idris~\cite{idris})
which allow
the compile-time computation of types which depend on data,
Dependent types have already been proposed
for low-level programming~\cite{CHAGN07}, generic programming~\cite{AM03}
and metaprogramming~\cite{Chl10}.

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
\caption{Type rules for simple finite dependent types}
\label{simple-types}
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
One implementation sets $\kw{T}$ to be $\kw{unit}$,
but the next sets $\kw{T}$ to be $\kw{bool}$:
\begin{code}
/a[1,0,1]/ = (
  /zerop/ ,
  /unitp/ ,
  /epsilon/ ,
  /epsilon/ ) /quad/
/a[1,0,2]/ = (
  /onep/ ,
  /boolp/ ,
  /false/ ,
  /epsilon/ )
\end{code}
Bumping the minor version requires an implementation with a compatible interface,
for example:
\begin{code}
/A[1,1]/ = &
  /prodp/ /size/ /in/ /word/ /cdot/
  /prodp/ /T/ /in/ /FSet/(/size/) \\&\indent /cdot/ 
  /prodp/ /z/ /in/ /T/ /cdot/
  /prodp/ /s/ /in/ /reference/(/T/ /rightarrow/ /T/) /cdot/
  /unitp/
\end{code}
which can be implemented by setting $\kw{T}$ to be $\kw{word}$:
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
systems~\cite{McQ86, HMM90, Har93}. In some ways, dependency management is simpler
because the dependency graph is acyclic,
but it does introduce interface evolution complexity,
for example Rust's~\cite[\#1105]{rfcs}.

\subsection{Finite dependencies}

\begin{comment}
\begin{code}
/binary/ :  ∀ {j} (k : 𝔹 ↑ j) → FSet(k)
\end{code}
\end{comment}

One feature that all of these examples have in common is that they do not
require any infinite data. Existing dependent type systems encourage the
use of in1finite types such such as lists or trees.
The prototypical infinite types are $\mathbb{N}$ (the type of natural
numbers) and $\kw{Set}$ (the type of types). This is a mismatch with systems
programs, where types are often \emph{sized} (for example in Rust,
types are \texttt{Sized} by default~\cite[\S3.31]{rust-book}).
In particular, systems programs are usually parameterized by
$\kw{WORDSIZE}$, and assume that data fits into memory
(for example that arrays are indexed by a word, not by a natural number).

A simple language of finite types is given in Figure~\ref{simple-types}.
In this language, all types are finite, in particular
$\kw{FSet}(n) \in \kw{FSet}(\kw{one} + n)$
(the size is slightly arbitrary, we could have chosen any increasing
size, for instance $\kw{FSet}(n) \in \kw{FSet}(\kw{one} \ll n)$).

The system is based on a theory of binary arithmetic, but even
that is definable within the language, for example the type
of bitstrings is definable by induction:
\begin{code}
/binary/ = /indn/
           (/FSet/)
           (/unitp/)
           (/fn/ n /cdot/ /fn/ A /cdot/ (/bool/ /times/ A))
\end{code}
For example:
\begin{code}
%WORDSIZE =
  /WORDSIZE/ &/in/ /binary/(/WORDSIZE/)
\end{code}
Some issues finite types raise include:
\begin{description}

\item[Induction:]
  As the type for $\kw{WORDSIZE}$ suggests,
  this is all spookily cyclic. In particular, binary numbers
  are parameterized by their bitlength, which is itself
  a binary number. An induction principal is needed,
  even if it is extra-logical, similar to
  Agda's universe polymorphism~\cite{agda}. We hypothesize
  that a theory of irrelevant natural numbers might suffice.

\item[Path types:] Dependent type systems usually come with an identity type $a
  \equiv_A b$ where $a : A$ and $b : A$.
  If identity types are interpreted as paths as in Homotopy Type Theory~\cite{hott},
  then the size of $A \equiv_{\kw{FSet}(n)} B$ is at most the size of $A \rightarrow B$,
  which would suggest considering $(a \equiv_A b) \in \kw{FSet}(n \ll n)$
  when $A \in \kw{FSet}(n)$.
  This makes the type of identities over $A$ much larger than the type of $A$,
  which may give problems with, for example, codings of indexed types.

\item[Theory of binary arithmetic:]
  The theory of finite types is very dependent on the theory of natural
  numbers, and it is very easy to end up type checking dependant on
  properties such as associativity and commutativity of addition.
  Such theorems could be handled by an SMT solver, but this has its own
  issues, such as the interaction between the SMT solver and type
  inference, and the complexity of an SMT solver being visible to
  the end programmer.

\item[Pointers]
  In systems programming languages such as Rust, cyclic data structures
  are mediated by pointers. In a finite type system, we could allow a
  type of pointers $\&(A)$ where $\&(A) \in \kw{FSet}(\kw{WORDSIZE})$
  when $A \in \kw{FSet}(n)$.
  Pointer creation can fail in low-memory situations, so should be
  encapsulated in a monad, similar to Haskell's $\kw{ST}$ monad.
  Care needs to be taken about pointers to data which includes sets,
  in particular $\&(\kw{FSet}(\kw{WORDSIZE})) \in
  \kw{FSet}(\kw{WORDSIZE})$ is very close to introducing unsoundness.

\end{description}
More research is needed!

\section{Conclusions}

Dependent types are a good fit for some of the more difficult problems
with programming in the large: metaprogramming and dependency management.
Howeever, their focus on infinite types is a mismatch.
Systems are finite, and are better served by systems which
encourage the use of finite types.

\sloppy
\bibliographystyle{plain}
\bibliography{finite-dtypes}

\end{document}

