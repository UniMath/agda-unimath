---
title: Univalent Mathematics in Agda
---

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundations.identity-types where

open import foundations.dependent-pair-types using (Σ; pair)
open import foundations.functions using (id; _∘_)
open import foundations.levels using (UU; Level)
```

##  The identity type

```agda
data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

{-# BUILTIN EQUALITY Id  #-}
```

In the following definition we give a construction of path induction.
However, in the development of this library we will mostly use Agda's
built-in methods to give constructions by path induction.

```agda
ind-Id :
  {i j : Level} {A : UU i} (x : A) (B : (y : A) (p : Id x y) → UU j) →
  (B x refl) → (y : A) (p : Id x y) → B y p
ind-Id x B b y refl = b
```

## The groupoidal structure of types

We introduce the groupoidal operations on identity types. The fact that they
are equivalences is recorded in `equivalences`.

```agda
module _
  {l : Level} {A : UU l}
  where
  
  _∙_ : {x y z : A} → Id x y → Id y z → Id x z
  refl ∙ q = q

  concat : {x y : A} → Id x y → (z : A) → Id y z → Id x z
  concat p z q = p ∙ q

  concat' : (x : A) {y z : A} → Id y z → Id x y → Id x z
  concat' x q p = p ∙ q

  inv : {x y : A} → Id x y → Id y x
  inv refl = refl
```

## The groupoidal laws for types

```agda
module _
  {l : Level} {A : UU l}
  where
  
  assoc :
    {x y z w : A} (p : Id x y) (q : Id y z) (r : Id z w) →
    Id ((p ∙ q) ∙ r) (p ∙ (q ∙ r))
  assoc refl q r = refl

  left-unit : {x y : A} {p : Id x y} → Id (refl ∙ p) p
  left-unit = refl
  
  right-unit : {x y : A} {p : Id x y} → Id (p ∙ refl) p
  right-unit {p = refl} = refl
  
  left-inv : {x y : A} (p : Id x y) → Id ((inv p) ∙ p) refl
  left-inv refl = refl
  
  right-inv : {x y : A} (p : Id x y) → Id (p ∙ (inv p)) refl
  right-inv refl = refl
  
  inv-inv : {x y : A} (p : Id x y) → Id (inv (inv p)) p
  inv-inv refl = refl
```

## The action on paths of functions

```agda
ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) →
  Id (f x) (f y)
ap f refl = refl

ap-id :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) → Id (ap id p) p
ap-id refl = refl

ap-comp :
  {i j k : Level} {A : UU i} {B : UU j} {C : UU k} (g : B → C)
  (f : A → B) {x y : A} (p : Id x y) → Id (ap (g ∘ f) p) (ap g (ap f p))
ap-comp g f refl = refl

ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') → Id (f x y) (f x' y')
ap-binary f refl refl = refl

triangle-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap-binary f p q) (ap (λ z → f z y) p ∙ ap (f x') q)
triangle-ap-binary f refl refl = refl

triangle-ap-binary' :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y y' : B} (q : Id y y') →
  Id (ap-binary f p q) (ap (f x) q ∙ ap (λ z → f z y') p)
triangle-ap-binary' f refl refl = refl

left-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x : A} {y y' : B} (q : Id y y') →
  Id (ap-binary f refl q) (ap (f x) q)
left-unit-ap-binary f refl = refl

right-unit-ap-binary :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C) →
  {x x' : A} (p : Id x x') {y : B} →
  Id (ap-binary f p refl) (ap (λ z → f z y) p)
right-unit-ap-binary f refl = refl

ap-refl :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) (x : A) →
  Id (ap f (refl {_} {_} {x})) refl
ap-refl f x = refl

ap-concat :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y z : A}
  (p : Id x y) (q : Id y z) → Id (ap f (p ∙ q)) ((ap f p) ∙ (ap f q))
ap-concat f refl q = refl

ap-inv :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A}
  (p : Id x y) → Id (ap f (inv p)) (inv (ap f p))
ap-inv f refl = refl
```

## Transport

We introduce transport. The fact that `tr B p` is an equivalence is recorded in `equivalences`.

```agda
tr :
  {i j : Level} {A : UU i} (B : A → UU j) {x y : A} (p : Id x y) → B x → B y
tr B refl b = b

apd :
  {i j : Level} {A : UU i} {B : A → UU j} (f : (x : A) → B x) {x y : A}
  (p : Id x y) → Id (tr B p (f x)) (f y)
apd f refl = refl

path-over :
  {i j : Level} {A :  UU i} (B : A → UU j) {x x' : A} (p : Id x x') →
  B x → B x' → UU j
path-over B p y y' = Id (tr B p y) y'

refl-path-over :
  {i j : Level} {A : UU i} (B : A → UU j) (x : A) (y : B x) →
  path-over B refl y y
refl-path-over B x y = refl
```

### laws for transport

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where
  
  tr-concat :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y z : A} (p : Id x y)
    (q : Id y z) (b : B x) → Id (tr B (p ∙ q) b) (tr B q (tr B p b))
  tr-concat refl q b = refl

  eq-transpose-tr :
    {x y : A} (p : Id x y) {u : B x} {v : B y} →
    Id v (tr B p u) → Id (tr B (inv p) v) u
  eq-transpose-tr refl q = q

  eq-transpose-tr' :
    {x y : A} (p : Id x y) {u : B x} {v : B y} →
    Id (tr B p u) v → Id u (tr B (inv p) v)
  eq-transpose-tr' refl q = q

tr-ap :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} {D : C → UU l4}
  (f : A → C) (g : (x : A) → B x → D (f x)) {x y : A} (p : Id x y) (z : B x) →
  Id (tr D (ap f p) (g x z)) (g y (tr B p z))
tr-ap f g refl z = refl
```

## Distributivity of inv over concat

```agda
distributive-inv-concat :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A}
  (q : Id y z) → Id (inv (p ∙ q)) ((inv q) ∙ (inv p))
distributive-inv-concat refl refl = refl
```

## Transposing inverses

The fact that `inv-con` and `con-inv` are equivalences is recorded in `equivalences`.

```agda
inv-con :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id q ((inv p) ∙ r)
inv-con refl q r = id 

con-inv :
  {i : Level} {A : UU i} {x y : A} (p : Id x y) {z : A} (q : Id y z)
  (r : Id x z) → (Id (p ∙ q) r) → Id p (r ∙ (inv q))
con-inv p refl r =
  ( λ α → α ∙ (inv right-unit)) ∘ (concat (inv right-unit) r)
```

## The path lifting property

```agda
lift :
  {i j : Level} {A : UU i} {B : A → UU j} {x y : A} (p : Id x y)
  (b : B x) → Id (pair x b) (pair y (tr B p b))
lift refl b = refl
```

## The Mac Lane pentagon for identity types

```agda
Mac-Lane-pentagon :
  {i : Level} {A : UU i} {a b c d e : A}
  (p : Id a b) (q : Id b c) (r : Id c d) (s : Id d e) →
  let α₁ = (ap (λ t → t ∙ s) (assoc p q r))
      α₂ = (assoc p (q ∙ r) s)
      α₃ = (ap (λ t → p ∙ t) (assoc q r s))
      α₄ = (assoc (p ∙ q) r s)
      α₅ = (assoc p q (r ∙ s))
  in
  Id ((α₁ ∙ α₂) ∙ α₃) (α₄ ∙ α₅)
Mac-Lane-pentagon refl refl refl refl = refl
```

## Commuting squares of identifications

```agda
square :
  {l1 : Level} {A : UU l1} {x y1 y2 z : A}
  (p-left : Id x y1) (p-bottom : Id y1 z)
  (p-top : Id x y2) (p-right : Id y2 z) → UU l1
square p-left p-bottom p-top p-right = Id (p-left ∙ p-bottom) (p-top ∙ p-right)

sq-left-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A} {p1 p1' : Id x y1}
  (s : Id p1 p1') {q1 : Id y1 z} {p2 : Id x y2} {q2 : Id y2 z} →
  square p1 q1 p2 q2 → square p1' q1 p2 q2
sq-left-whisk refl sq = sq

sq-top-whisk :
  {i : Level} {A : UU i} {x y1 y2 z : A}
  (p1 : Id x y1) (q1 : Id y1 z)
  (p2 : Id x y2) {p2' : Id x y2} (s : Id p2 p2') (q2 : Id y2 z) →
  square p1 q1 p2 q2 → square p1 q1 p2' q2
sq-top-whisk p1 q1 p2 refl q2 sq = sq
```
