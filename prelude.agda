{-# OPTIONS --type-in-type #-} -- DANGER!
postulate HOLE : {A : Set} -> A -- MORE DANGER!

infixr 3 [_
infixr 5 _,_
infixr 7 _]

infixr 5 _/xor/_
infixr 2 typeof
infixr 2 dtypeof
infixr 2 &_
infixr 2 _\\
infixl 1 WHEN
infixl 1 AND

-- Definitions used in the main body

data ⊥ : Set where

record ⊤ : Set where
  constructor /zero/

record Π (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field fst : A
  field snd : B(fst)

syntax Π A (\x -> B) = Π x ∈ A ∙ B

_×_ : Set → Set → Set
(A × B) = Π x ∈ A ∙ B

data 𝔹 : Set where
  /0/ : 𝔹
  /1/ : 𝔹

if_then_else_ : ∀ {A : 𝔹 -> Set} -> (b : 𝔹) -> A(/1/) -> A(/0/) -> A(b)
if /0/ then T else F = F
if /1/ then T else F = T

⟨_⟩ : 𝔹 → Set
⟨ /0/ ⟩ = ⊥
⟨ /1/ ⟩ = ⊤

data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

one = succ zero
two = succ one
three = succ two
four = succ three

_+n_ : ℕ → ℕ → ℕ
zero +n k = k
(succ j) +n k = succ(j +n k)

_↑_ : Set → ℕ → Set
(A ↑ zero) = ⊤
(A ↑ (succ n)) = (A × (A ↑ n))

/IF/_/THEN/_/ELSE/_ : forall {A : 𝔹 -> Set} -> (b : 𝔹) -> A(/1/) -> A(/0/) -> A(b)
/IF/ /0/ /THEN/ T /ELSE/ F = F
/IF/ /1/ /THEN/ T /ELSE/ F = T

-- Binary arithmetic

/padding/ : ∀ {k} → (𝔹 ↑ k)
/padding/ {zero}   = /zero/
/padding/ {succ k} = (/0/ , /padding/)

/one/ : (𝔹 ↑ one)
/one/ = (/1/ , /zero/)

/IMPOSSIBLE/ : {A : Set} → {{p : ⊥}} → A
/IMPOSSIBLE/ {A} {{()}}

/not/ : 𝔹 → 𝔹
/not/ /0/ = /1/
/not/ /1/ = /0/

/extend/ : ∀ {k} → (𝔹 ↑ k) → (𝔹 ↑ succ k)
/extend/ {zero}   _       = (/0/ , /zero/)
/extend/ {succ k} (b , n) = (b , /extend/ n)

_/land/_ : 𝔹 → 𝔹 → 𝔹
(/0/ /land/ b) = /0/
(/1/ /land/ b) = b

_/lor/_ : 𝔹 → 𝔹 → 𝔹
(/0/ /lor/ b) = b
(/1/ /lor/ b) = /1/

/neg/ : 𝔹 → 𝔹
/neg/ /0/ = /1/
/neg/ /1/ = /0/

_/xor/_ : 𝔹 → 𝔹 → 𝔹
(/0/ /xor/ b) = b
(/1/ /xor/ b) = /neg/ b

/carry/ : 𝔹 → 𝔹 → 𝔹 → 𝔹
/carry/ /0/ a b = a /land/ b
/carry/ /1/ a b = a /lor/ b

addclen : ∀ {j k} → 𝔹 → (𝔹 ↑ j) → (𝔹 ↑ k) → ℕ
addclen {zero} {k}      /0/ m n = k
addclen {zero} {zero} /1/ m n = one
addclen {zero} {succ k} /1/ m (b , n) = succ (addclen b m n)
addclen {succ j} {zero}   /0/ m n = succ j
addclen {succ j} {zero}   /1/ (a , m) n = succ (addclen a m n)
addclen {succ j} {succ k} c   (a , m) (b , n) = succ (addclen (/carry/ c a b) m n)

addlen : ∀ {j k} → (𝔹 ↑ j) → (𝔹 ↑ k) → ℕ
addlen = addclen /0/

/addc/ : ∀ {j k} c → (m : 𝔹 ↑ j) → (n : 𝔹 ↑ k) → (𝔹 ↑ addclen c m n)
/addc/ {zero}   {k}      /0/ m n = n
/addc/ {zero} {zero} /1/ m n = /one/
/addc/ {zero} {succ k} /1/ m (b , n) = (/not/ b , /addc/ b m n)
/addc/ {succ j} {zero}   /0/ (a , m) n = (a , m)
/addc/ {succ j} {zero}   /1/ (a , m) n = (/not/ a , /addc/ a m n)
/addc/ {succ j} {succ k} c (a , m) (b , n) = ((c /xor/ a /xor/ b) , (/addc/ (/carry/ c a b) m n))

_+_ : ∀ {j k} → (m : 𝔹 ↑ j) → (n : 𝔹 ↑ k) → (𝔹 ↑ addlen m n)
_+_ = /addc/ /0/

/succ/ : ∀ {k} → (n : 𝔹 ↑ k) → (𝔹 ↑ addclen /1/ /zero/ n)
/succ/ = /addc/ /1/ /zero/

indn : ∀ {k} {A : Set} → A → (A → A) → (𝔹 ↑ k) → A
indn {zero}   e f n = e
indn {succ k} e f (/0/ , n) = indn e (λ x → f (f x)) n
indn {succ k} e f (/1/ , n) = f (indn e (λ x → f (f x)) n)

unary : ∀ {k} → (𝔹 ↑ k) → ℕ
unary = indn zero succ

dindn : {A : ∀ {k} → (𝔹 ↑ k) → Set} → (∀ {k} → A {k} /padding/) → (∀ {k} (n : 𝔹 ↑ k) → A(n) → A(/succ/(n))) → ∀ {k} → (n : 𝔹 ↑ k) → A(n)
dindn {A} e f {zero} n = e
dindn {A} e f {succ k} (/0/ , n) = dindn {λ {j} m → A (/0/ , m)} e (λ {j} m x → f (/1/ , m) (f (/0/ , m) x)) n
dindn {A} e f {succ k} (/1/ , n) = f (/0/ , n) (dindn {λ {j} m → A (/0/ , m)} e (λ {j} m x → f (/1/ , m) (f (/0/ , m) x)) n)

_++_ : ∀ {A j k} → (A ↑ j) → (A ↑ k) → (A ↑ (j +n k))
_++_ {A} {zero}   xs       ys = ys
_++_ {A} {succ j} (x , xs) ys = (x , xs ++ ys)

_/ll/_ : ∀ {j k} → (𝔹 ↑ j) → (n : 𝔹 ↑ k) → (𝔹 ↑ (j +n unary n))
(m /ll/ n) = (m ++ /padding/)

/truncate?/ : ∀ {k} → (n : 𝔹 ↑ succ(k)) → 𝔹
/truncate?/ {zero}   (/0/ , _) = /1/
/truncate?/ {zero}   (/1/ , _) = /0/
/truncate?/ {succ k} (_   , n) = /truncate?/ n

/truncate/ : ∀ {k} → (n : 𝔹 ↑ succ(k)) → {{p : ⟨ /truncate?/ n ⟩}} → (𝔹 ↑ k)
/truncate/ {zero}   (/0/ , _) = /zero/
/truncate/ {zero}   (/1/ , _) = /IMPOSSIBLE/
/truncate/ {succ k} (b   , n) = (b , /truncate/ n)

-- Finite sets

EncodableIn : ∀ {k} → Set → (𝔹 ↑ k) → Set
EncodableIn = HOLE

record FSet {k} (n : 𝔹 ↑ k) : Set where
  field Carrier : Set
  field .encodable : EncodableIn Carrier n
open FSet public

/sizeof/ : ∀ {k} → {n : 𝔹 ↑ k} → FSet(n) → (𝔹 ↑ k)
/sizeof/ {k} {n} A = n

/FSet/ : ∀ {k} -> (n : 𝔹 ↑ k) -> FSet(/one/ + n)
/FSet/ n = record { Carrier = FSet(n); encodable = HOLE }

/empty/ : FSet(/zero/)
/empty/ = record { Carrier = ⊥; encodable = HOLE }

/bool/ : FSet(/one/)
/bool/ = record { Carrier = 𝔹; encodable = HOLE }

/unit/ : FSet(/zero/)
/unit/ = record { Carrier = ⊤; encodable = HOLE }

/bits/ : ∀ {k} (n : 𝔹 ↑ k) ->  FSet(n)
/bits/ n = record { Carrier = (𝔹 ↑ unary n); encodable = HOLE }

/PI/ : ∀ {j k} -> {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} -> (A : FSet(m)) -> (Carrier(A) → FSet(n)) -> FSet(m + n)
/PI/ A B = record { Carrier = Π x ∈ (Carrier A) ∙ Carrier (B x) ; encodable = HOLE }

syntax /PI/ A (λ x → B) = /prod/ x /in/ A /cdot/ B

/SIGMA/ : ∀ {j k} -> {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} -> (A : FSet(m)) → ((Carrier A) → FSet(n)) -> FSet(n /ll/ m)
/SIGMA/ A B = record { Carrier = (x : Carrier A) → (Carrier (B x)) ; encodable = HOLE }

syntax /SIGMA/ A (λ x → B) = /sum/ x /in/ A /cdot/ B

-- Stuff to help with LaTeX layout

typeof : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → (Carrier A) → Set
typeof A x = Carrier A

dtypeof : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → (Carrier A → Set) → Set
dtypeof A F = ∀ x → F x

WHEN : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → (Carrier A → Set) → Set
WHEN A F = ∀ x → F x

AND : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → (Carrier A → Set) → Set
AND A F = ∀ x → F x

[_ : ∀ {A k} → (A ↑ k) → (A ↑ k)
[_ x = x

_] : ∀ {A} → A → (A ↑ one)
_] x = (x , /zero/)

_\\ : forall {A : Set} -> A -> A
x \\ = x

&_ : forall {A : Set} -> A -> A
& x = x

syntax typeof A x = x &/in/ A
syntax dtypeof A (λ x → B) = x /in/ A /implies/ B
syntax WHEN A (λ x → B) = B &/WHEN/ x /in/ A
syntax AND A (λ x → B) = B /AND/ x /in/ A
