\documentclass{article}

\usepackage{amsfonts}
\usepackage{ucs}
\usepackage[utf8x]{inputenc}
\usepackage{verbatim}
\usepackage{finite-dtypes}

\begin{document}

\title{Finite Dependent Types}
\author{Alan Jeffrey}

\maketitle

% Set up the basic definitions.
\begin{comment}
\begin{code}
{-# OPTIONS --type-in-type #-} -- WARNING, CLAXONS!
open import prelude
\end{code}
\end{comment}

\section{Hacking around with Agda}

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

\end{document}


