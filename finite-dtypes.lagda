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

% Set up the basic definitions.
\begin{comment}
\begin{code}
{-# OPTIONS --type-in-type #-} -- WARNING, CLAXONS!
open import prelude -- POSTULATES LIVE HERE!
\end{code}
\end{comment}

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

One feature that all of these formalisms have in common is that they support
types with an infinite number of elements, such as lists or trees.
The prototypical infinite types are $\mathbb{N}$ (the type of natural
numbers) and $\keyword{Set}$ (the type of types). This is a mismatch with systems
programs, where types are often \emph{sized} (for example in Rust,
types are \texttt{Sized}~\cite[\S3.31]{rust-book} by default).
In particular, systems programs are usually parameterized by the
architectures word size, and assume that data fits into memory
(for example that arrays are indexed by a word, not by a natural number).

In this position paper, we encourage the exploration of programming
languages in which finite types are the norm. In \S\ref{hacking} we
present a simple system for finite types, where $\keyword{bits}(k)$
replaces $\mathbb{N}$ and $\keyword{FSet}(k)$ replaces $\keyword{Set}$.
In each case $k$ is the bitlength of the type, for example
if we define $\keyword{two} = [\keyword{0},\keyword{1}]$
and $\keyword{three} = [\keyword{1},\keyword{1}]$
then $\keyword{two} \in \keyword{bits}(\keyword{two}) \in \keyword{FSet}(\keyword{two}) \in \keyword{FSet}(\keyword{three})$.

This system is not fully developed (\emph{hey, this is a position paper!})
in particular its use of $\keyword{FSet}(k) \in \keyword{FSet}(k+1)$
is possibly unsound, and its encoding in Agda uses $\keyword{Set} \in \keyword{Set}$
which is dangerous. \S\ref{hacking} is written in Literate Agda, and has
been typechecked with Agda~v2.4.2.5. The source is available~\cite{self}.

\section{Hacking around with Agda}
\label{hacking}

For this paper, we will go old-school, and assume a word size of eight bits.
Binary is encoded little-endian:
\begin{code}
/WORDSIZE/ = & [ /0/ , /0/ , /0/ , /1/ , /0/ , /0/ , /0/ , /0/ ] \\
/word/ = & /bits/ (/WORDSIZE/)
\end{code}
This appears to be spookily cyclic!
\begin{code}
%WORDSIZE =
  /WORDSIZE/ &/in/ /word/ \\
%word =
  /word/ &/in/ /FSet/(/WORDSIZE/)
\end{code}
% Types of things defined in this section.
\begin{comment}
\begin{code}
_/times/_ : ∀ {k} {m n : 𝔹 ↑ k} → (FSet m) -> (FSet n) -> (FSet(m + n))
_/rightarrow/_ : ∀ {j k} {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} → (A : FSet m) -> (FSet n) -> (FSet (n /ll/ m))
_/oplus/_ : ∀ {k} {m : 𝔹 ↑ k} → (FSet m) → (FSet m) → (FSet (/one/ + m))
/inl/ : ∀ {k} → {n : 𝔹 ↑ k} → {A B : FSet(n)} → Carrier(/sum/ x /in/ A /cdot/ (A /oplus/ B))
/inr/ : ∀ {k} → {n : 𝔹 ↑ k} → {A B : FSet(n)} → Carrier(/sum/ y /in/ B /cdot/ (A /oplus/ B))
_/?/ : ∀ {k} {m : 𝔹 ↑ k} → (FSet m) → (FSet (/one/ + m))
/some/ : ∀ {k} → {n : 𝔹 ↑ k} → {A : FSet(n)} → Carrier(/sum/ x /in/ A /cdot/ (A /?/))
/none/ : ∀ {k} → {n : 𝔹 ↑ k} → {A : FSet(n)} → Carrier(A /?/)
\end{code}
\end{comment}
The definition of independent pairs in terms of dependent pairs:
\begin{code}
(A /times/ B) = /prod/ x /in/ A /cdot/ B
\end{code}
The definition of independent functions in terms of dependent functions:
\begin{code}
(A /rightarrow/ B) = /sum/ x /in/ A /cdot/ B
\end{code}
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
/none/ = & /inr/(/padding/)
\end{code}
Derived typing rules:
\begin{code}
%times = forall k -> (m n : 𝔹 ↑ succ k) ->
  (A /times/ B) &/in/ /FSet/(m + n)
  &/WHEN/ A /in/ /FSet/(m)
  /AND/ B /in/ /FSet/(n) \\
%rightarrow = forall j k -> (m : 𝔹 ↑ succ j) -> (n : 𝔹 ↑ succ k) ->
  (A /rightarrow/ B) &/in/ /FSet/(n /ll/ m)
  &/WHEN/ A /in/ /FSet/(m)
  /AND/ B /in/ /FSet/(n) \\
%oplus = forall k -> (n : 𝔹 ↑ k) ->
  (A /oplus/ B) &/in/ /FSet/(/one/ + n)
  &/WHEN/ A /in/ /FSet/(n)
  /AND/ B /in/ /FSet/(n) \\
%? = forall k -> (n : 𝔹 ↑ k) ->
  (A /?/) &/in/ /FSet/(/one/ + n)
  &/WHEN/ A /in/ /FSet/(n)
\end{code}
Built-in types:
\begin{code}
%unit =
  /unit/ &/in/ /FSet/(/zero/) \\
%bool = 
  /bool/ &/in/ /FSet/(/one/) \\
%prod = forall j k -> (m : 𝔹 ↑ j) -> (n : 𝔹 ↑ k) ->
  (/prod/ x /in/ A /cdot/ B(x)) &/in/ /FSet/(m + n)
  &/WHEN/ B /in/ (A /rightarrow/ /FSet/(n))
  /AND/ A /in/ /FSet/(m) \\
%sum = forall j k -> (m : 𝔹 ↑ j) -> (n : 𝔹 ↑ k) ->
  (/sum/ x /in/ A /cdot/ B(x)) &/in/ /FSet/ (n /ll/ m)
  &/WHEN/ B /in/ (A /rightarrow/ /FSet/(n))
  /AND/ A /in/ /FSet/(m) \\
%FSet = forall k -> (n : 𝔹 ↑ k) ->
  /FSet/(n) &/in/ /FSet/(/one/ + n)
\end{code}

\sloppy
\bibliographystyle{plain}
\bibliography{finite-dtypes}

\end{document}


