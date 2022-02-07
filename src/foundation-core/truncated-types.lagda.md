# Truncated types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.truncated-types where

open import foundation-core.contractible-types using
  ( is-contr; eq-is-contr; is-contr-is-equiv; is-contr-retract-of)
open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.embeddings using
  ( is-emb; _↪_; map-emb; is-emb-map-emb)
open import foundation-core.equivalences using
  ( is-equiv; _≃_; map-inv-is-equiv; is-equiv-map-inv-is-equiv)
open import foundation-core.identity-types using (Id; refl; left-inv; ap)
open import foundation-core.retractions using (_retract-of_; retract-eq)
open import foundation-core.truncation-levels using (𝕋; neg-two-𝕋; succ-𝕋)
open import foundation-core.universe-levels using (Level; UU; lsuc)
```

## Idea

The truncatedness of a type is a measure of the complexity of its identity types. The simplest case is a contractible type. This is the base case of the inductive definition of truncatedness for types. A type is (k+1)-truncated if its identity types are k-truncated.

## Definition

### The condition of truncatedness

```agda
is-trunc : {i : Level} (k : 𝕋) → UU i → UU i
is-trunc neg-two-𝕋 A = is-contr A
is-trunc (succ-𝕋 k) A = (x y : A) → is-trunc k (Id x y)
```

### The universe of truncated types

```agda
UU-Truncated-Type : (l : Level) → 𝕋 → UU (lsuc l)
UU-Truncated-Type l k = Σ (UU l) (is-trunc k)

module _
  {k : 𝕋} {l : Level}
  where
  
  type-Truncated-Type : UU-Truncated-Type l k → UU l
  type-Truncated-Type = pr1

  abstract
    is-trunc-type-Truncated-Type :
      (A : UU-Truncated-Type l k) → is-trunc k (type-Truncated-Type A)
    is-trunc-type-Truncated-Type = pr2
```

## Properties

### If a type is k-truncated, then it is (k+1)-truncated.

```agda
abstract
  is-trunc-succ-is-trunc :
    (k : 𝕋) {i : Level} {A : UU i} → is-trunc k A → is-trunc (succ-𝕋 k) A
  pr1 (is-trunc-succ-is-trunc neg-two-𝕋 H x y) = eq-is-contr H
  pr2 (is-trunc-succ-is-trunc neg-two-𝕋 H x .x) refl = left-inv (pr2 H x)
  is-trunc-succ-is-trunc (succ-𝕋 k) H x y = is-trunc-succ-is-trunc k (H x y)

truncated-type-succ-Truncated-Type :
  (k : 𝕋) {l : Level} → UU-Truncated-Type l k → UU-Truncated-Type l (succ-𝕋 k)
pr1 (truncated-type-succ-Truncated-Type k A) = type-Truncated-Type A
pr2 (truncated-type-succ-Truncated-Type k A) =
  is-trunc-succ-is-trunc k (is-trunc-type-Truncated-Type A)
```

### The identity type of a k-truncated type is k-truncated

```agda
abstract
  is-trunc-Id :
    {l : Level} {k : 𝕋} {A : UU l} →
    is-trunc k A → (x y : A) → is-trunc k (Id x y)
  is-trunc-Id {l} {k}= is-trunc-succ-is-trunc k

Id-Truncated-Type :
  {l : Level} {k : 𝕋} (A : UU-Truncated-Type l (succ-𝕋 k)) →
  (x y : type-Truncated-Type A) → UU-Truncated-Type l k
pr1 (Id-Truncated-Type A x y) = Id x y
pr2 (Id-Truncated-Type A x y) = is-trunc-type-Truncated-Type A x y

Id-Truncated-Type' :
  {l : Level} {k : 𝕋} (A : UU-Truncated-Type l k) →
  (x y : type-Truncated-Type A) → UU-Truncated-Type l k
pr1 (Id-Truncated-Type' A x y) = Id x y
pr2 (Id-Truncated-Type' A x y) =
  is-trunc-Id (is-trunc-type-Truncated-Type A) x y
```

### k-truncated types are closed under retracts

```agda
module _
  {l1 l2 : Level}
  where

  is-trunc-retract-of :
    {k : 𝕋} {A : UU l1} {B : UU l2} →
    A retract-of B → is-trunc k B → is-trunc k A
  is-trunc-retract-of {neg-two-𝕋} = is-contr-retract-of _
  is-trunc-retract-of {succ-𝕋 k} R H x y =
    is-trunc-retract-of (retract-eq R x y) (H (pr1 R x) (pr1 R y))
```

### k-truncated types are closed under equivalences

```agda
abstract
  is-trunc-is-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU j) (f : A → B) → is-equiv f →
    is-trunc k B → is-trunc k A
  is-trunc-is-equiv k B f is-equiv-f =
    is-trunc-retract-of (pair f (pr2 is-equiv-f))

abstract
  is-trunc-equiv :
    {i j : Level} (k : 𝕋) {A : UU i} (B : UU  j) (e : A ≃ B) →
    is-trunc k B → is-trunc k A
  is-trunc-equiv k B (pair f is-equiv-f) =
    is-trunc-is-equiv k B f is-equiv-f

abstract
  is-trunc-is-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (f : A → B) →
    is-equiv f → is-trunc k A → is-trunc k B
  is-trunc-is-equiv' k A  f is-equiv-f is-trunc-A =
    is-trunc-is-equiv k A
      ( map-inv-is-equiv is-equiv-f)
      ( is-equiv-map-inv-is-equiv is-equiv-f)
      ( is-trunc-A)

abstract
  is-trunc-equiv' :
    {i j : Level} (k : 𝕋) (A : UU i) {B : UU j} (e : A ≃ B) →
    is-trunc k A → is-trunc k B
  is-trunc-equiv' k A (pair f is-equiv-f) =
    is-trunc-is-equiv' k A f is-equiv-f

```

### If a type embeds into a (k+1)-truncated type, then it is (k+1)-truncated

```agda
abstract
  is-trunc-is-emb :
    {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} (f : A → B) →
    is-emb f → is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-is-emb k f Ef H x y =
    is-trunc-is-equiv k (Id (f x) (f y)) (ap f {x} {y}) (Ef x y) (H (f x) (f y))

abstract
  is-trunc-emb :
    {i j : Level} (k : 𝕋) {A : UU i} {B : UU j} (f : A ↪ B) →
    is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) A
  is-trunc-emb k f = is-trunc-is-emb k (map-emb f) (is-emb-map-emb f)
```
