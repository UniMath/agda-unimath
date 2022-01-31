# Precomposing maps

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.precomposition where

open import foundation.coherently-invertible-maps using
  ( is-coherently-invertible)
open import foundation.constant-maps using (const)
open import foundation.contractible-maps using (is-contr-map-is-equiv)
open import foundation.contractible-types using (center; eq-is-contr')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; is-equiv-has-inverse; _≃_; map-equiv; is-equiv-map-equiv;
    map-inv-is-equiv; issec-map-inv-is-equiv)
open import foundation.function-extensionality using (eq-htpy; htpy-eq)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_; refl-htpy)
open import foundation.identity-types using (Id; refl; tr; ap; _∙_; apd)
open import foundation.path-split-maps using
  ( is-coherently-invertible-is-path-split; is-path-split-is-equiv)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop-type-Prop; is-prop)
open import foundation.sets using (UU-Set; type-Set; is-set-type-Set; is-set)
open import foundation.truncated-types using
  ( UU-Truncated-Type; type-Truncated-Type; is-trunc-type-Truncated-Type;
    is-trunc)
open import foundation.truncation-levels using (𝕋; neg-two-𝕋; succ-𝕋)
open import foundation.unit-type using (unit; star)
open import foundation.universe-levels using (Level; UU; lzero)
```

## Idea

Precomposing a function `g : B → C` by `f : A → B` gives the function `g ∘ f : A → C`. In other words, precomposition by `f` is a map `- ∘ f : (B → C) → (A → C)`. More generally, precomposition can be defined for dependent functions.

## Definition

```agda
precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3) →
  ((b : B) → C b) → ((a : A) → C (f a))
precomp-Π f C h a = h (f a)

precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : UU l3) →
  (B → C) → (A → C)
precomp f C = precomp-Π f (λ b → C)
```

## Properties

### If `f` is coherently invertible, then precomposing by `f` is an equivalence

```agda
tr-precompose-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
  (f : A → B) {x y : A} (p : Id x y) → tr C (ap f p) ~ tr (λ x → C (f x)) p
tr-precompose-fam C f refl = refl-htpy

abstract
  is-equiv-precomp-Π-is-coherently-invertible :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-coherently-invertible f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-coherently-invertible f
    ( pair g (pair issec-g (pair isretr-g coh))) C = 
    is-equiv-has-inverse
      (λ s y → tr C (issec-g y) (s (g y)))
      ( λ s → eq-htpy (λ x → 
        ( ap (λ t → tr C t (s (g (f x)))) (coh x)) ∙
        ( ( tr-precompose-fam C f (isretr-g x) (s (g (f x)))) ∙
          ( apd s (isretr-g x)))))
      ( λ s → eq-htpy λ y → apd s (issec-g y))
```

### If `f` is an equivalence, then precomposing by `f` is an equivalence

```agda
abstract
  is-equiv-precomp-Π-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : B → UU l3) → is-equiv (precomp-Π f C)
  is-equiv-precomp-Π-is-equiv f is-equiv-f =
    is-equiv-precomp-Π-is-coherently-invertible f
      ( is-coherently-invertible-is-path-split f
        ( is-path-split-is-equiv f is-equiv-f))

equiv-precomp-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) →
  (C : B → UU l3) → ((b : B) → C b) ≃ ((a : A) → C (map-equiv e a))
pr1 (equiv-precomp-Π e C) = precomp-Π (map-equiv e) C
pr2 (equiv-precomp-Π e C) =
  is-equiv-precomp-Π-is-equiv (map-equiv e) (is-equiv-map-equiv e) C
```

### Equivalences can be seen as constructors for inductive types.

```agda
abstract
  ind-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f) →
    ((x : A) → C (f x)) → ((y : B) → C y)
  ind-is-equiv C f is-equiv-f =
    map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C)
  
  comp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3)
    (f : A → B) (is-equiv-f : is-equiv f) (h : (x : A) → C (f x)) →
    Id (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) h
  comp-is-equiv C f is-equiv-f h =
    issec-map-inv-is-equiv (is-equiv-precomp-Π-is-equiv f is-equiv-f C) h
  
  htpy-comp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    (C : B → UU l3) (f : A → B) (is-equiv-f : is-equiv f)
    (h : (x : A) → C (f x)) →
    (λ x → (ind-is-equiv C f is-equiv-f h) (f x)) ~ h
  htpy-comp-is-equiv C f is-equiv-f h = htpy-eq (comp-is-equiv C f is-equiv-f h)
```

## If dependent precomposition by `f` is an equivalence, then precomposition by `f` is an equivalence

```agda
abstract
  is-equiv-precomp-is-equiv-precomp-Π :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((C : B → UU l3) → is-equiv (precomp-Π f C)) →
    ((C : UU l3) → is-equiv (precomp f C))
  is-equiv-precomp-is-equiv-precomp-Π f is-equiv-precomp-Π-f C =
    is-equiv-precomp-Π-f (λ y → C)
```

### If `f` is an equivalence, then precomposition by `f` is an equivalence

```agda
abstract
  is-equiv-precomp-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) → is-equiv f →
    (C : UU l3) → is-equiv (precomp f C)
  is-equiv-precomp-is-equiv f is-equiv-f =
    is-equiv-precomp-is-equiv-precomp-Π f
      ( is-equiv-precomp-Π-is-equiv f is-equiv-f)

equiv-precomp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B) (C : UU l3) →
  (B → C) ≃ (A → C)
pr1 (equiv-precomp e C) = precomp (map-equiv e) C
pr2 (equiv-precomp e C) =
  is-equiv-precomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) C
```

### If precomposing by `f` is an equivalence, then `f` is an equivalence

First, we prove this relative to a subuniverse, such that `f` is a map between two types in that subuniverse.

```agda
abstract
  is-equiv-is-equiv-precomp-subuniverse :
    { l1 l2 : Level}
    ( α : Level → Level) (P : (l : Level) → UU l → UU (α l))
    ( A : Σ (UU l1) (P l1)) (B : Σ (UU l2) (P l2)) (f : pr1 A → pr1 B) →
    ( (l : Level) (C : Σ (UU l) (P l)) →
      is-equiv (precomp f (pr1 C))) →
    is-equiv f
  is-equiv-is-equiv-precomp-subuniverse α P A B f is-equiv-precomp-f =
    let retr-f = center (is-contr-map-is-equiv (is-equiv-precomp-f _ A) id) in
    is-equiv-has-inverse
      ( pr1 retr-f)
      ( htpy-eq
        ( ap ( pr1)
             ( eq-is-contr'
               ( is-contr-map-is-equiv (is-equiv-precomp-f _ B) f)
                 ( pair
                   ( f ∘ (pr1 retr-f))
                   ( ap (λ (g : pr1 A → pr1 A) → f ∘ g) (pr2 retr-f)))
                 ( pair id refl))))
      ( htpy-eq (pr2 retr-f))
```

Now we prove the usual statement, without the subuniverse

```agda
abstract
  is-equiv-is-equiv-precomp :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    ((l : Level) (C : UU l) → is-equiv (precomp f C)) → is-equiv f
  is-equiv-is-equiv-precomp {A = A} {B = B} f is-equiv-precomp-f =
    is-equiv-is-equiv-precomp-subuniverse
      ( const Level Level lzero)
      ( λ l X → unit)
      ( pair A star)
      ( pair B star)
      ( f)
      ( λ l C → is-equiv-precomp-f l (pr1 C))
```

```agda
is-equiv-is-equiv-precomp-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2)
  (f : type-Prop P → type-Prop Q) →
  ({l : Level} (R : UU-Prop l) → is-equiv (precomp f (type-Prop R))) →
  is-equiv f
is-equiv-is-equiv-precomp-Prop P Q f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-prop) P Q f (λ l → H {l})

is-equiv-is-equiv-precomp-Set :
  {l1 l2 : Level} (A : UU-Set l1) (B : UU-Set l2)
  (f : type-Set A → type-Set B) →
  ({l : Level} (C : UU-Set l) → is-equiv (precomp f (type-Set C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Set A B f H =
  is-equiv-is-equiv-precomp-subuniverse id (λ l → is-set) A B f (λ l → H {l})

is-equiv-is-equiv-precomp-Truncated-Type :
  {l1 l2 : Level} (k : 𝕋)
  (A : UU-Truncated-Type k l1) (B : UU-Truncated-Type k l2)
  (f : type-Truncated-Type A → type-Truncated-Type B) →
  ({l : Level} (C : UU-Truncated-Type k l) → is-equiv (precomp f (pr1 C))) →
  is-equiv f
is-equiv-is-equiv-precomp-Truncated-Type k A B f H =
    is-equiv-is-equiv-precomp-subuniverse id (λ l → is-trunc k) A B f
      ( λ l → H {l})
```
