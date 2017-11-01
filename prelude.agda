-- Definitions used in the main body

_\\ : forall {A : Set} -> A -> A
x \\ = x

&_ : forall {A : Set} -> A -> A
& x = x

data /bool/ : Set where
  /0/ : /bool/
  /1/ : /bool/

/IF/_/THEN/_/ELSE/_ : forall {A : /bool/ -> Set} -> (b : /bool/) -> A(/1/) -> A(/0/) -> A(b)
/IF/ /0/ /THEN/ T /ELSE/ F = F
/IF/ /1/ /THEN/ T /ELSE/ F = T

data /nat/ : Set where
  /0/ : /nat/
  /1/+ : /nat/ -> /nat/

record /unit/ : Set where
  constructor /epsilon/
  
record /Pi/ (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field fst : A
  field snd : B(fst)

syntax  /Pi/ A (\x -> B) = /Pi/ x /in/ A /cdot/ B

data _/equiv/_ {A : Set} (x : A) : A -> Set where
  /refl/ : (x /equiv/ x)
