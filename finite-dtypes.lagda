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

% Some Agda preliminaries

\begin{comment}
\begin{code}

_\\ : forall {A : Set} -> A -> A
x \\ = x

&_ : forall {A : Set} -> A -> A
& x = x

data /bool/ : Set where
  /true/ : /bool/
  /false/ : /bool/

\end{code}
\end{comment}

\section{Introduction}

Just checking that negation still works!
\begin{comment}
\begin{code}
/not/ : /bool/ -> /bool/
\end{code}
\end{comment}
\begin{code}
/not/(/true/)  = & /false/ \\
/not/(/false/) = & /true/
\end{code}


\end{document}


