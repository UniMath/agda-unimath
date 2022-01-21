---
title: Formalisation of the Symmetry Book
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.04-inductive-types where

open import foundations.03-natural-numbers public
```

## The unit type

```agda
data unit : UU lzero where
  star : unit

ind-unit : {l : Level} {P : unit → UU l} → P star → ((x : unit) → P x)
ind-unit p star = p

terminal-map : {l : Level} {A : UU l} → A → unit
terminal-map a = star

raise-unit : (l : Level) → UU l
raise-unit l = raise l unit

raise-star : {l : Level} → raise l unit
raise-star = map-raise star
```

## The empty type

```agda
data empty : UU lzero where

𝟘 = empty

ind-empty : {l : Level} {P : empty → UU l} → ((x : empty) → P x)
ind-empty ()

ex-falso : {l : Level} {A : UU l} → empty → A
ex-falso = ind-empty

raise-empty : (l : Level) → UU l
raise-empty l = raise l empty

¬ : {l : Level} → UU l → UU l
¬ A = A → empty

is-empty : {l : Level} → UU l → UU l
is-empty = ¬

is-nonempty : {l : Level} → UU l → UU l
is-nonempty A = ¬ (is-empty A)

functor-neg : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬ Q → ¬ P)
functor-neg f nq p = nq (f p)
```

## The booleans

```agda
data bool : UU lzero where
  true false : bool

{-# BUILTIN BOOL bool #-}
{-# BUILTIN TRUE  true  #-}
{-# BUILTIN FALSE false #-}
```

### The boolean operators

```agda
neg-bool : bool → bool
neg-bool true = false
neg-bool false = true

conjunction-bool : bool → (bool → bool)
conjunction-bool true true = true
conjunction-bool true false = false
conjunction-bool false true = false
conjunction-bool false false = false

disjunction-bool : bool → (bool → bool)
disjunction-bool true true = true
disjunction-bool true false = true
disjunction-bool false true = true
disjunction-bool false false = false
```

## Coproducts

```agda
data coprod {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)  where
  inl : A → coprod A B
  inr : B → coprod A B

ind-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : coprod A B) → C t
ind-coprod C f g (inl x) = f x
ind-coprod C f g (inr x) = g x

map-coprod :
  {l1 l2 l1' l2' : Level} {A : UU l1} {B : UU l2} {A' : UU l1'} {B' : UU l2'} →
  (A → A') → (B → B') → coprod A B → coprod A' B'
map-coprod f g (inl x) = inl (f x)
map-coprod f g (inr y) = inr (g y)

map-right-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty B → coprod A B → A
map-right-unit-law-coprod-is-empty A B nb (inl a) = a
map-right-unit-law-coprod-is-empty A B nb (inr b) = ex-falso (nb b)

map-left-unit-law-coprod-is-empty :
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → is-empty A → coprod A B → B
map-left-unit-law-coprod-is-empty A B na (inl a) = ex-falso (na a)
map-left-unit-law-coprod-is-empty A B na (inr b) = b
```

## Dependent pair types

```agda
record Σ {l1 l2} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1

open Σ public

{-# BUILTIN SIGMA Σ #-}

ind-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : A) (y : B x) → C (pair x y)) → ((t : Σ A B) → C t)
ind-Σ f (pair x y) = f x y

ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (pair x y)
ev-pair f x y = f (pair x y)
```

## Cartesian products

```agda
prod : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
prod A B = Σ A (λ a → B)

pair' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A → B → prod A B
pair' = pair

_×_ :  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A × B = prod A B

map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) → (A × B) → (C × D)
pr1 (map-prod f g (pair a b)) = f a
pr2 (map-prod f g (pair a b)) = g b
```

## The type of integers

```agda
ℤ : UU lzero
ℤ = coprod ℕ (coprod unit ℕ)
```

- Inclusion of the negative integers

```agda
in-neg : ℕ → ℤ
in-neg n = inl n
```

- Negative one

```agda
neg-one-ℤ : ℤ
neg-one-ℤ = in-neg zero-ℕ
```

- Zero

```agda
zero-ℤ : ℤ
zero-ℤ = inr (inl star)
```

- One

```agda
one-ℤ : ℤ
one-ℤ = inr (inr zero-ℕ)
```

- Inclusion of the positive integers

```agda
in-pos : ℕ → ℤ
in-pos n = inr (inr n)
```

- Inclusion of the natural numbers

```agda
int-ℕ : ℕ → ℤ
int-ℕ zero-ℕ = zero-ℤ
int-ℕ (succ-ℕ n) = in-pos n
```

- Induction principle on the type of integers

```agda
ind-ℤ :
  {l : Level} (P : ℤ → UU l) →
  P neg-one-ℤ → ((n : ℕ) → P (inl n) → P (inl (succ-ℕ n))) →
  P zero-ℤ →
  P one-ℤ → ((n : ℕ) → P (inr (inr (n))) → P (inr (inr (succ-ℕ n)))) →
  (k : ℤ) → P k
ind-ℤ P p-1 p-S p0 p1 pS (inl zero-ℕ) = p-1
ind-ℤ P p-1 p-S p0 p1 pS (inl (succ-ℕ x)) =
  p-S x (ind-ℤ P p-1 p-S p0 p1 pS (inl x))
ind-ℤ P p-1 p-S p0 p1 pS (inr (inl star)) = p0
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr zero-ℕ)) = p1
ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (succ-ℕ x))) =
  pS x (ind-ℤ P p-1 p-S p0 p1 pS (inr (inr (x))))
```

- The successor and predecessor functions on ℤ

```agda
succ-ℤ : ℤ → ℤ
succ-ℤ (inl zero-ℕ) = zero-ℤ
succ-ℤ (inl (succ-ℕ x)) = inl x
succ-ℤ (inr (inl star)) = one-ℤ
succ-ℤ (inr (inr x)) = inr (inr (succ-ℕ x))

pred-ℤ : ℤ → ℤ
pred-ℤ (inl x) = inl (succ-ℕ x)
pred-ℤ (inr (inl star)) = inl zero-ℕ
pred-ℤ (inr (inr zero-ℕ)) = inr (inl star)
pred-ℤ (inr (inr (succ-ℕ x))) = inr (inr x)
```

### Arithmetic operations on the integers

- Addition on ℤ

```agda
add-ℤ : ℤ → ℤ → ℤ
add-ℤ (inl zero-ℕ) l = pred-ℤ l
add-ℤ (inl (succ-ℕ x)) l = pred-ℤ (add-ℤ (inl x) l)
add-ℤ (inr (inl star)) l = l
add-ℤ (inr (inr zero-ℕ)) l = succ-ℤ l
add-ℤ (inr (inr (succ-ℕ x))) l = succ-ℤ (add-ℤ (inr (inr x)) l)

add-ℤ' : ℤ → ℤ → ℤ
add-ℤ' x y = add-ℤ y x
```

- The negative of an integer

```agda
neg-ℤ : ℤ → ℤ
neg-ℤ (inl x) = inr (inr x)
neg-ℤ (inr (inl star)) = inr (inl star)
neg-ℤ (inr (inr x)) = inl x
```

- Multiplication of integers

We give two definitions of multiplication on ℤ

```agda
mul-ℤ : ℤ → ℤ → ℤ
mul-ℤ (inl zero-ℕ) l = neg-ℤ l
mul-ℤ (inl (succ-ℕ x)) l = add-ℤ (neg-ℤ l) (mul-ℤ (inl x) l)
mul-ℤ (inr (inl star)) l = zero-ℤ
mul-ℤ (inr (inr zero-ℕ)) l = l
mul-ℤ (inr (inr (succ-ℕ x))) l = add-ℤ l (mul-ℤ (inr (inr x)) l)

mul-ℤ' : ℤ → ℤ → ℤ
mul-ℤ' x y = mul-ℤ y x

explicit-mul-ℤ : ℤ → ℤ → ℤ
explicit-mul-ℤ (inl x) (inl y) = int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y))
explicit-mul-ℤ (inl x) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inl x) (inr (inr y)) =
  neg-ℤ (int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))
explicit-mul-ℤ (inr (inl star)) (inl y) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inl y) =
  neg-ℤ (int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y)))
explicit-mul-ℤ (inr (inl star)) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inr (inl star)) (inr (inr y)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inl star)) = zero-ℤ
explicit-mul-ℤ (inr (inr x)) (inr (inr y)) = int-ℕ (mul-ℕ (succ-ℕ x) (succ-ℕ y))

explicit-mul-ℤ' : ℤ → ℤ → ℤ
explicit-mul-ℤ' x y = explicit-mul-ℤ y x
```

##  Logical equivalence

```agda
_↔_ : {l1 l2 : Level} → UU l1 → UU l2 → UU (l1 ⊔ l2)
A ↔ B = (A → B) × (B → A)

_∘iff_ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (B ↔ C) → (A ↔ B) → (A ↔ C)
pr1 (pair g1 g2 ∘iff pair f1 f2) = g1 ∘ f1
pr2 (pair g1 g2 ∘iff pair f1 f2) = f2 ∘ g2
```

## Double negation

```agda
¬¬ : {l : Level} → UU l → UU l
¬¬ P = ¬ (¬ P)

¬¬¬ : {l : Level} → UU l → UU l
¬¬¬ P = ¬ (¬ (¬ P))

intro-dn : {l : Level} {P : UU l} → P → ¬¬ P
intro-dn p f = f p

functor-dn : {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → Q) → (¬¬ P → ¬¬ Q)
functor-dn f = functor-neg (functor-neg f)

```

```agda
no-fixed-points-neg :
  {l : Level} (A : UU l) → ¬ ((A → ¬ A) × (¬ A → A))
no-fixed-points-neg A (pair f g) =
  ( λ (h : ¬ A) → h (g h)) (λ (a : A) → f a a)
```

In this exercise we were asked to show that $A + ¬A$ implies $¬¬A → A$.
We get double negation elimination for the types that are  decidable.

```agda
dn-elim-is-decidable :
  {l : Level} (P : UU l) → coprod P (¬ P) → (¬¬ P → P)
dn-elim-is-decidable P (inl x) p = x
dn-elim-is-decidable P (inr x) p = ex-falso (p x)

dn-is-decidable : {l : Level} {P : UU l} → ¬¬ (coprod P (¬ P))
dn-is-decidable {P = P} f =
  functor-neg (inr {A = P} {B = ¬ P}) f
    ( functor-neg (inl {A = P} {B = ¬ P}) f)

dn-dn-elim : {l : Level} {P : UU l} → ¬¬ (¬¬ P → P)
dn-dn-elim {P = P} f =
  ( λ (np : ¬ P) → f (λ (nnp : ¬¬ P) → ex-falso (nnp np)))
    ( λ (p : P) → f (λ (nnp : ¬¬ P) → p))
```

## Double negations of classical laws

```agda
Peirces-law :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (((P → Q) → P) → P)
Peirces-law {P = P} {Q} f =
  ( λ (np : ¬ P) → f (λ h → h (λ p → ex-falso (np p))))
  ( λ (p : P) → f (λ h → p))

dn-linearity-implication :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (coprod (P → Q) (Q → P))
dn-linearity-implication {P = P} {Q = Q} f =
  ( λ (np : ¬ P) →
    functor-neg (inl {A = P → Q} {B = Q → P}) f (λ p → ex-falso (np p)))
    ( λ (p : P) →
      functor-neg (inr {A = P → Q} {B = Q → P}) f (λ q → p))
```

## Cases of double negation elimination

```agda
dn-elim-neg : {l : Level} (P : UU l) → ¬¬¬ P → ¬ P
dn-elim-neg P f p = f (λ g → g p)

dn-extend :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  (P → ¬¬ Q) → (¬¬ P → ¬¬ Q)
dn-extend {P = P} {Q = Q} f = dn-elim-neg (¬ Q) ∘ (functor-dn f)

dn-elim-exp :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ (P → ¬¬ Q) → (P → ¬¬ Q)
dn-elim-exp {P = P} {Q = Q} f p =
  dn-elim-neg (¬ Q) (functor-dn (λ (g : P → ¬¬ Q) → g p) f)

dn-elim-prod :
  {l1 l2 : Level} {P : UU l1} {Q : UU l2} →
  ¬¬ ((¬¬ P) × (¬¬ Q)) → (¬¬ P) × (¬¬ Q)
pr1 (dn-elim-prod {P = P} {Q = Q} f) = dn-elim-neg (¬ P) (functor-dn pr1 f)
pr2 (dn-elim-prod {P = P} {Q = Q} f) = dn-elim-neg (¬ Q) (functor-dn pr2 f)
```

## Lists

```agda
data list {l : Level} (A : UU l) : UU l where
  nil : list A
  cons : A → list A → list A

in-list : {l : Level} {A : UU l} → A → list A
in-list a = cons a nil
```

## Operations on lists

```agda
fold-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  list A → B
fold-list b μ nil = b
fold-list b μ (cons a l) = μ a (fold-list b μ l)

length-list : {l : Level} {A : UU l} → list A → ℕ
length-list = fold-list zero-ℕ (λ a → succ-ℕ)

sum-list-ℕ : list ℕ → ℕ
sum-list-ℕ = fold-list zero-ℕ add-ℕ

product-list-ℕ : list ℕ → ℕ
product-list-ℕ = fold-list one-ℕ mul-ℕ

concat-list : {l : Level} {A : UU l} → list A → (list A → list A)
concat-list {l} {A} = fold-list id (λ a f → (cons a) ∘ f)

flatten-list : {l : Level} {A : UU l} → list (list A) → list A
flatten-list = fold-list nil concat-list

reverse-list : {l : Level} {A : UU l} → list A → list A
reverse-list nil = nil
reverse-list (cons a l) = concat-list (reverse-list l) (in-list a)
```
