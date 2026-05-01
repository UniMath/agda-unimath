# Tuples

```agda
module lists.tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.homotopies
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-higher-homotopies-composition

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

For every [natural number](elementary-number-theory.natural-numbers.md) `n` we
define {{#concept "tuples" WD="n-tuple" WDID=Q600590 Agda=tuple}} of length `n`.
These are [equivalent](lists.equivalence-tuples-finite-sequences.md) to the
related concept of [finite sequences](lists.finite-sequences.md), but are
structured like [lists](lists.lists.md) instead of [arrays](lists.arrays.md).

## Definitions

### The type of tuples

```agda
infixr 10 _∷_

data tuple {l : Level} (A : UU l) : ℕ → UU l where
  empty-tuple : tuple A zero-ℕ
  _∷_ : {n : ℕ} → A → tuple A n → tuple A (succ-ℕ n)

module _
  {l : Level} {A : UU l}
  where

  head-tuple : {n : ℕ} → tuple A (succ-ℕ n) → A
  head-tuple (x ∷ v) = x

  tail-tuple : {n : ℕ} → tuple A (succ-ℕ n) → tuple A n
  tail-tuple (x ∷ v) = v

  snoc-tuple : {n : ℕ} → tuple A n → A → tuple A (succ-ℕ n)
  snoc-tuple empty-tuple a = a ∷ empty-tuple
  snoc-tuple (x ∷ v) a = x ∷ (snoc-tuple v a)

  revert-tuple : {n : ℕ} → tuple A n → tuple A n
  revert-tuple empty-tuple = empty-tuple
  revert-tuple (x ∷ v) = snoc-tuple (revert-tuple v) x

  all-tuple : {l2 : Level} {n : ℕ} → (P : A → UU l2) → tuple A n → UU l2
  all-tuple P empty-tuple = raise-unit _
  all-tuple P (x ∷ v) = P x × all-tuple P v

  component-tuple :
    (n : ℕ) → tuple A n → Fin n → A
  component-tuple (succ-ℕ n) (a ∷ v) (inl k) = component-tuple n v k
  component-tuple (succ-ℕ n) (a ∷ v) (inr k) = a

  infix 6 _∈-tuple_
  data _∈-tuple_ : {n : ℕ} → A → tuple A n → UU l where
    is-head : {n : ℕ} (a : A) (l : tuple A n) → a ∈-tuple (a ∷ l)
    is-in-tail :
      {n : ℕ} (a x : A) (l : tuple A n) → a ∈-tuple l → a ∈-tuple (x ∷ l)

  index-in-tuple : (n : ℕ) → (a : A) → (v : tuple A n) → a ∈-tuple v → Fin n
  index-in-tuple (succ-ℕ n) a (.a ∷ v) (is-head .a .v) =
    inr star
  index-in-tuple (succ-ℕ n) a (x ∷ v) (is-in-tail .a .x .v I) =
    inl (index-in-tuple n a v I)

  eq-component-tuple-index-in-tuple :
    (n : ℕ) (a : A) (v : tuple A n) (I : a ∈-tuple v) →
    a ＝ component-tuple n v (index-in-tuple n a v I)
  eq-component-tuple-index-in-tuple (succ-ℕ n) a (.a ∷ v) (is-head .a .v) = refl
  eq-component-tuple-index-in-tuple
    (succ-ℕ n) a (x ∷ v) (is-in-tail .a .x .v I) =
    eq-component-tuple-index-in-tuple n a v I
```

## Properties

### Characterizing equality of tuples

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-tuple : (n : ℕ) → tuple A n → tuple A n → UU l
  Eq-tuple zero-ℕ empty-tuple empty-tuple = raise-unit l
  Eq-tuple (succ-ℕ n) (x ∷ xs) (y ∷ ys) = (x ＝ y) × (Eq-tuple n xs ys)

  refl-Eq-tuple : (n : ℕ) → (u : tuple A n) → Eq-tuple n u u
  refl-Eq-tuple zero-ℕ empty-tuple = map-raise star
  pr1 (refl-Eq-tuple (succ-ℕ n) (x ∷ xs)) = refl
  pr2 (refl-Eq-tuple (succ-ℕ n) (x ∷ xs)) = refl-Eq-tuple n xs

  Eq-eq-tuple : (n : ℕ) → (u v : tuple A n) → u ＝ v → Eq-tuple n u v
  Eq-eq-tuple n u .u refl = refl-Eq-tuple n u

  eq-Eq-tuple : (n : ℕ) → (u v : tuple A n) → Eq-tuple n u v → u ＝ v
  eq-Eq-tuple zero-ℕ empty-tuple empty-tuple eq-tuple = refl
  eq-Eq-tuple (succ-ℕ n) (x ∷ xs) (.x ∷ ys) (refl , eqs) =
    ap (x ∷_) (eq-Eq-tuple n xs ys eqs)

  is-retraction-eq-Eq-tuple :
    (n : ℕ) → (u v : tuple A n) →
    (p : u ＝ v) → eq-Eq-tuple n u v (Eq-eq-tuple n u v p) ＝ p
  is-retraction-eq-Eq-tuple zero-ℕ empty-tuple empty-tuple refl = refl
  is-retraction-eq-Eq-tuple (succ-ℕ n) (x ∷ xs) .(x ∷ xs) refl =
    left-whisker-comp² (x ∷_) (is-retraction-eq-Eq-tuple n xs xs) refl

  square-Eq-eq-tuple :
    (n : ℕ) (x : A) (u v : tuple A n) (p : u ＝ v) →
    (Eq-eq-tuple _ (x ∷ u) (x ∷ v) (ap (x ∷_) p)) ＝
    (refl , (Eq-eq-tuple n u v p))
  square-Eq-eq-tuple zero-ℕ x empty-tuple empty-tuple refl = refl
  square-Eq-eq-tuple (succ-ℕ n) a (x ∷ xs) (.x ∷ .xs) refl = refl

  is-section-eq-Eq-tuple :
    (n : ℕ) (u v : tuple A n) →
    (p : Eq-tuple n u v) → Eq-eq-tuple n u v (eq-Eq-tuple n u v p) ＝ p
  is-section-eq-Eq-tuple zero-ℕ empty-tuple empty-tuple (map-raise star) = refl
  is-section-eq-Eq-tuple (succ-ℕ n) (x ∷ xs) (.x ∷ ys) (refl , ps) =
    ( square-Eq-eq-tuple n x xs ys (eq-Eq-tuple n xs ys ps)) ∙
    ( eq-pair-eq-fiber (is-section-eq-Eq-tuple n xs ys ps))

  is-equiv-Eq-eq-tuple :
    (n : ℕ) → (u v : tuple A n) → is-equiv (Eq-eq-tuple n u v)
  is-equiv-Eq-eq-tuple n u v =
    is-equiv-is-invertible
      ( eq-Eq-tuple n u v)
      ( is-section-eq-Eq-tuple n u v)
      ( is-retraction-eq-Eq-tuple n u v)

  extensionality-tuple : (n : ℕ) → (u v : tuple A n) → (u ＝ v) ≃ Eq-tuple n u v
  extensionality-tuple n u v = (Eq-eq-tuple n u v , is-equiv-Eq-eq-tuple n u v)
```

### The type of tuples of elements in a truncated type is truncated

#### The type of listed tuples of elements in a truncated type is truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  is-trunc-Eq-tuple :
    (k : 𝕋) (n : ℕ) → is-trunc (succ-𝕋 k) A →
    (u v : tuple A n) → is-trunc (k) (Eq-tuple n u v)
  is-trunc-Eq-tuple k zero-ℕ A-trunc empty-tuple empty-tuple =
    is-trunc-is-contr k is-contr-raise-unit
  is-trunc-Eq-tuple k (succ-ℕ n) A-trunc (x ∷ xs) (y ∷ ys) =
    is-trunc-product k (A-trunc x y) (is-trunc-Eq-tuple k n A-trunc xs ys)

  center-is-contr-tuple :
    {n : ℕ} → is-contr A → tuple A n
  center-is-contr-tuple {zero-ℕ} H = empty-tuple
  center-is-contr-tuple {succ-ℕ n} H = center H ∷ center-is-contr-tuple {n} H

  contraction-is-contr-tuple' :
    {n : ℕ} (H : is-contr A) → (v : tuple A n) →
    Eq-tuple n (center-is-contr-tuple H) v
  contraction-is-contr-tuple' {zero-ℕ} H empty-tuple =
    refl-Eq-tuple {l} {A} 0 empty-tuple
  pr1 (contraction-is-contr-tuple' {succ-ℕ n} H (x ∷ v)) =
    eq-is-contr H
  pr2 (contraction-is-contr-tuple' {succ-ℕ n} H (x ∷ v)) =
    contraction-is-contr-tuple' {n} H v

  contraction-is-contr-tuple :
    {n : ℕ} (H : is-contr A) → (v : tuple A n) → (center-is-contr-tuple H) ＝ v
  contraction-is-contr-tuple {n} H v =
    eq-Eq-tuple n (center-is-contr-tuple H) v (contraction-is-contr-tuple' H v)

  is-contr-tuple :
    {n : ℕ} → is-contr A → is-contr (tuple A n)
  pr1 (is-contr-tuple H) = center-is-contr-tuple H
  pr2 (is-contr-tuple H) = contraction-is-contr-tuple H

  is-trunc-tuple :
    (k : 𝕋) → (n : ℕ) → is-trunc k A → is-trunc k (tuple A n)
  is-trunc-tuple neg-two-𝕋 n H = is-contr-tuple H
  is-trunc-tuple (succ-𝕋 k) n H x y =
    is-trunc-equiv k
      ( Eq-tuple n x y)
      ( extensionality-tuple n x y)
      ( is-trunc-Eq-tuple k n H x y)
```

### The type of tuples of elements in a set is a set

#### The type of listed tuples of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-tuple : (n : ℕ) → is-set A → is-set (tuple A n)
  is-set-tuple = is-trunc-tuple zero-𝕋

tuple-Set : {l : Level} → Set l → ℕ → Set l
pr1 (tuple-Set A n) = tuple (type-Set A) n
pr2 (tuple-Set A n) = is-set-tuple n (is-set-type-Set A)
```

### Adding the tail to the head gives the same tuple

```agda
module _
  {l : Level} {A : UU l}
  where

  cons-head-tail-tuple :
    (n : ℕ) →
    (v : tuple A (succ-ℕ n)) →
    ((head-tuple v) ∷ (tail-tuple v)) ＝ v
  cons-head-tail-tuple n (x ∷ v) = refl
```

### Computing the transport of a tuple over its size

```agda
compute-tr-tuple :
  {l : Level} {A : UU l}
  {n m : ℕ} (p : succ-ℕ n ＝ succ-ℕ m) (v : tuple A n) (x : A) →
  tr (tuple A) p (x ∷ v) ＝
  (x ∷ tr (tuple A) (is-injective-succ-ℕ p) v)
compute-tr-tuple refl v x = refl
```
