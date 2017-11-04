{-# OPTIONS --type-in-type #-} -- DANGER!
postulate HOLE : {A : Set} -> A -- MORE DANGER!

infixr 6 _\\
infixr 6 _\\&\indent
infixl 2 &_

infixr 3 [_
infixr 5 _,_
infixr 7 _]

infixr 5 _/xor/_ _/land/_ _/lor/_
infixr 5 /Sigma/ /Pi/ lambda
infixr 2 id
infixl 1 WHEN
infixl 1 AND

-- Definitions used in the main body

data ⊥ : Set where

record ⊤ : Set where
  constructor /epsilon/

record Π (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field fst : A
  field snd : B(fst)

syntax Π A (\x -> B) = Π x ∈ A ∙ B

_×_ : Set → Set → Set
(A × B) = Π x ∈ A ∙ B

data 𝔹 : Set where
  /false/ : 𝔹
  /true/ : 𝔹

if_then_else_ : ∀ {A : 𝔹 -> Set} -> (b : 𝔹) -> A(/true/) -> A(/false/) -> A(b)
if /false/ then T else F = F
if /true/ then T else F = T

⟨_⟩ : 𝔹 → Set
⟨ /false/ ⟩ = ⊥
⟨ /true/ ⟩ = ⊤

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

/IF/_/THEN/_/ELSE/_ : forall {A : 𝔹 -> Set} -> (b : 𝔹) -> A(/true/) -> A(/false/) -> A(b)
/IF/ /false/ /THEN/ T /ELSE/ F = F
/IF/ /true/ /THEN/ T /ELSE/ F = T

-- Binary arithmetic

indn : ∀ {k} {A : Set} → A → (A → A) → (𝔹 ↑ k) → A
indn {zero}   e f n = e
indn {succ k} e f (/false/ , n) = indn e (λ x → f (f x)) n
indn {succ k} e f (/true/ , n) = f (indn e (λ x → f (f x)) n)

unary : ∀ {k} → (𝔹 ↑ k) → ℕ
unary = indn zero succ

/zerop/ : ∀ {k} → (𝔹 ↑ k)
/zerop/ {zero}   = /epsilon/
/zerop/ {succ n} = (/false/ , /zerop/)

/epsilon/[_] :  ∀ {k} → (n : 𝔹 ↑ k) → (𝔹 ↑ unary n)
/epsilon/[ n ] = /zerop/

/onep/ : ∀ {k} → (𝔹 ↑ succ k)
/onep/ = (/true/ , /zerop/)

/one/ : (𝔹 ↑ one)
/one/ = /onep/

/max/ : ∀ {k} → (𝔹 ↑ k)
/max/ {zero}   = /epsilon/
/max/ {succ n} = (/true/ , /max/)

/IMPOSSIBLE/ : {A : Set} → {{p : ⊥}} → A
/IMPOSSIBLE/ {A} {{()}}

/not/ : 𝔹 → 𝔹
/not/ /false/ = /true/
/not/ /true/ = /false/

/extend/ : ∀ {k} → (𝔹 ↑ k) → (𝔹 ↑ succ k)
/extend/ {zero}   _       = (/false/ , /epsilon/)
/extend/ {succ k} (b , n) = (b , /extend/ n)

_/land/_ : 𝔹 → 𝔹 → 𝔹
(/false/ /land/ b) = /false/
(/true/ /land/ b) = b

_/lor/_ : 𝔹 → 𝔹 → 𝔹
(/false/ /lor/ b) = b
(/true/ /lor/ b) = /true/

/neg/ : 𝔹 → 𝔹
/neg/ /false/ = /true/
/neg/ /true/ = /false/

_/xor/_ : 𝔹 → 𝔹 → 𝔹
(/false/ /xor/ b) = b
(/true/ /xor/ b) = /neg/ b

/carry/ : 𝔹 → 𝔹 → 𝔹 → 𝔹
/carry/ /false/ a b = a /land/ b
/carry/ /true/ a b = a /lor/ b

addclen : ∀ {j k} → 𝔹 → (𝔹 ↑ j) → (𝔹 ↑ k) → ℕ
addclen {zero} {k}      /false/ m n = k
addclen {zero} {zero} /true/ m n = one
addclen {zero} {succ k} /true/ m (b , n) = succ (addclen b m n)
addclen {succ j} {zero}   /false/ m n = succ j
addclen {succ j} {zero}   /true/ (a , m) n = succ (addclen a m n)
addclen {succ j} {succ k} c   (a , m) (b , n) = succ (addclen (/carry/ c a b) m n)

addlen : ∀ {j k} → (𝔹 ↑ j) → (𝔹 ↑ k) → ℕ
addlen = addclen /false/

/addc/ : ∀ {j k} c → (m : 𝔹 ↑ j) → (n : 𝔹 ↑ k) → (𝔹 ↑ addclen c m n)
/addc/ {zero}   {k}      /false/ m n = n
/addc/ {zero} {zero} /true/ m n = /one/
/addc/ {zero} {succ k} /true/ m (b , n) = (/not/ b , /addc/ b m n)
/addc/ {succ j} {zero}   /false/ (a , m) n = (a , m)
/addc/ {succ j} {zero}   /true/ (a , m) n = (/not/ a , /addc/ a m n)
/addc/ {succ j} {succ k} c (a , m) (b , n) = ((c /xor/ a /xor/ b) , (/addc/ (/carry/ c a b) m n))

_+_ : ∀ {j k} → (m : 𝔹 ↑ j) → (n : 𝔹 ↑ k) → (𝔹 ↑ addlen m n)
_+_ = /addc/ /false/

/succ/ : ∀ {k} → (n : 𝔹 ↑ k) → (𝔹 ↑ addclen /true/ /epsilon/ n)
/succ/ = /addc/ /true/ /epsilon/

dindn : (A : ∀ {k} → (𝔹 ↑ k) → Set) → (∀ {k} → A(/zerop/ {k})) → (∀ {k} (n : 𝔹 ↑ k) → A(n) → A(/succ/(n))) → ∀ {k} → (n : 𝔹 ↑ k) → A(n)
dindn A e f {zero} n = e
dindn A e f {succ k} (/false/ , n) = dindn (λ {j} m → A (/false/ , m)) e (λ {j} m x → f (/true/ , m) (f (/false/ , m) x)) n
dindn A e f {succ k} (/true/ , n) = f (/false/ , n) (dindn (λ {j} m → A (/false/ , m)) e (λ {j} m x → f (/true/ , m) (f (/false/ , m) x)) n)

_++_ : ∀ {A j k} → (A ↑ j) → (A ↑ k) → (A ↑ (j +n k))
_++_ {A} {zero}   xs       ys = ys
_++_ {A} {succ j} (x , xs) ys = (x , xs ++ ys)

_/ll/_ : ∀ {j k} → (𝔹 ↑ j) → (n : 𝔹 ↑ k) → (𝔹 ↑ (j +n unary n))
(m /ll/ n) = (m ++ /zerop/)

/truncate/ : ∀ {j k} → (𝔹 ↑ j) → (𝔹 ↑ k)
/truncate/ {j} {zero} n = /epsilon/
/truncate/ {zero} {succ k} n = /zerop/
/truncate/ {succ j} {succ k} (a , n) = (a , /truncate/ n)

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

/nothingp/ : ∀ {k} → FSet(/zerop/ {k})
/nothingp/ = record { Carrier = ⊥; encodable = HOLE }

/nothing/[_] : ∀ {k} (n : 𝔹 ↑ k) → FSet(/zerop/ {unary n})
/nothing/[ n ] = /nothingp/

/nothing/ : FSet(/epsilon/)
/nothing/ = /nothingp/

/boolp/ : ∀ {k} → FSet(/onep/ {k})
/boolp/ = record { Carrier = 𝔹; encodable = HOLE }

/bool/ : FSet(/one/)
/bool/ = /boolp/

/unitp/ : ∀ {k} → FSet(/zerop/ {k})
/unitp/ = record { Carrier = ⊤; encodable = HOLE }

/unit/[_] : ∀ {k} (n : 𝔹 ↑ k) → FSet(/epsilon/[ n ])
/unit/[ n ] = /unitp/

/unit/ : FSet(/epsilon/)
/unit/ = /unit/[ /epsilon/ ]

/bits/ : ∀ {k} (n : 𝔹 ↑ k) ->  FSet(n)
/bits/ n = record { Carrier = (𝔹 ↑ unary n); encodable = HOLE }

/Pi/ : ∀ {j k} -> {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} -> (A : FSet(m)) -> (Carrier(A) → FSet(n)) -> FSet(m + n)
/Pi/ A B = record { Carrier = Π x ∈ (Carrier A) ∙ Carrier (B x) ; encodable = HOLE }

syntax /Pi/ A (λ x → B) = /prod/ x /in/ A /cdot/ B

/Sigma/ : ∀ {j k} -> {m : 𝔹 ↑ j} {n : 𝔹 ↑ k} -> (A : FSet(m)) → ((Carrier A) → FSet(n)) -> FSet(n /ll/ m)
/Sigma/ A B = record { Carrier = (x : Carrier A) → (Carrier (B x)) ; encodable = HOLE }

syntax /Sigma/ A (λ x → B) = /sum/ x /in/ A /cdot/ B

lambda : ∀ {A : Set} {B : A → Set} → (∀ x → B(x)) → (∀ x → B(x))
lambda f = f

syntax lambda (λ x → e) = /lambda/ x /cdot/ e

/indn/ :
  {h : ∀ {k} → (𝔹 ↑ k) → ℕ} →
  {g : ∀ {k} → (n : 𝔹 ↑ k) → (𝔹 ↑ h(n))} →
  (A : ∀ {k} → (n : 𝔹 ↑ k) → FSet(g(n))) →
  (∀ {k} → Carrier(A(/zerop/ {k}))) →
  (∀ {k} (n : 𝔹 ↑ k) → Carrier(A(n)) → Carrier(A(/one/ + n))) →
  ∀ {k} → (n : 𝔹 ↑ k) → Carrier(A(n))
/indn/ A e f = dindn (λ n → Carrier(A(n))) e (λ n x → g n (f n x)) where
  g : ∀ {k} → (n : 𝔹 ↑ k) → Carrier(A(/one/ + n)) → Carrier(A(/succ/(n)))
  g {zero}   n         x = x
  g {succ k} (/false/ , n) x = x
  g {succ k} (/true/ , n) x = x

-- Stuff to help with LaTeX layout

id : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → (Carrier A) → (Carrier A)
id A x = x

typeof : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → (Carrier A) → Set
typeof A x = Carrier A

WHEN : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → {B : Carrier A → Set} → (∀ x → B(x)) → (∀ x → B(x))
WHEN A F = F

AND : ∀ {k} → {n : 𝔹 ↑ k} → (A : FSet(n)) → {B : Carrier A → Set} → (∀ x → B(x)) → (∀ x → B(x))
AND A F = F

[_ : ∀ {A k} → (A ↑ k) → (A ↑ k)
[_ x = x

_] : ∀ {A} → A → (A ↑ one)
_] x = (x , /epsilon/)

_\\ : forall {A : Set} -> A -> A
x \\ = x

_\\&\indent : forall {A : Set} -> A -> A
x \\&\indent = x

&_ : forall {A : Set} -> A -> A
& x = x

syntax id A x = x &/in/ A
syntax WHEN A (λ x → B) = B &/WHEN/ x /in/ A
syntax AND A (λ x → B) = B /AND/ x /in/ A
