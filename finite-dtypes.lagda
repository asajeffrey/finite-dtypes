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

\begin{comment}
\begin{code}
-- Types of things defined in this section.
_/times/_ : Set -> Set -> Set
_/?/ : Set -> Set
/some/ : {A : Set} -> A -> A /?/
/none/ : {A : Set} -> A /?/
\end{code}
\end{comment}

The definition of independent product in terms of dependent product:
\begin{code}
(A /times/ B) = /Pi/ x /in/ A /cdot/ B
\end{code}
The definition of options in terms of dependent products:
\begin{code}
(A /?/) = & (/Pi/ b /in/ /bool/ /cdot/ (/IF/ b /THEN/ A /ELSE/ /unit/)) \\
/some/(x) = & (/1/ , x) \\
/none/ = & (/0/ , /epsilon/)
\end{code}

\end{document}


