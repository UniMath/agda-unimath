# Tuples

```agda
module linear-algebra.tuples where
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
open import foundation.function-extensionality
open import foundation.function-types
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

open import univalent-combinatorics.involution-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

There are two equivalent definitions of
{{#concept "tuples" WD="n-tuple" WDID=Q600590}} of length `n`. First, a
{{#concept "listed tuple" Agda=tuple}} of length `n` is a list of `n` elements
of type `A`. Secondly, a {{#concept "functional tuple" Agda=functional-tuple}}
of length `n` is a map from the
[standard finite type](univalent-combinatorics.standard-finite-types.md) of
cardinality `n` `Fin n` to `A`. We define both types of tuples and show that
they are equivalent.

## Definitions

### The type of listed tuples

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

### The functional type of tuples

```agda
functional-tuple : {l : Level} → UU l → ℕ → UU l
functional-tuple A n = Fin n → A

module _
  {l : Level} {A : UU l}
  where

  empty-functional-tuple : functional-tuple A 0
  empty-functional-tuple ()

  head-functional-tuple : (n : ℕ) → functional-tuple A (succ-ℕ n) → A
  head-functional-tuple n v = v (inr star)

  tail-functional-tuple :
    (n : ℕ) → functional-tuple A (succ-ℕ n) → functional-tuple A n
  tail-functional-tuple n v = v ∘ (inl-Fin n)

  cons-functional-tuple :
    (n : ℕ) → A → functional-tuple A n → functional-tuple A (succ-ℕ n)
  cons-functional-tuple n a v (inl x) = v x
  cons-functional-tuple n a v (inr x) = a

  snoc-functional-tuple :
    (n : ℕ) → functional-tuple A n → A → functional-tuple A (succ-ℕ n)
  snoc-functional-tuple zero-ℕ v a i = a
  snoc-functional-tuple (succ-ℕ n) v a (inl x) =
    snoc-functional-tuple n (tail-functional-tuple n v) a x
  snoc-functional-tuple (succ-ℕ n) v a (inr x) = head-functional-tuple n v

  revert-functional-tuple :
    (n : ℕ) → functional-tuple A n → functional-tuple A n
  revert-functional-tuple n v i = v (opposite-Fin n i)

  in-functional-tuple : (n : ℕ) → A → functional-tuple A n → UU l
  in-functional-tuple n a v = Σ (Fin n) (λ k → a ＝ v k)

  index-in-functional-tuple :
    (n : ℕ) (x : A) (v : functional-tuple A n) →
    in-functional-tuple n x v → Fin n
  index-in-functional-tuple n x v I = pr1 I

  eq-component-functional-tuple-index-in-functional-tuple :
    (n : ℕ) (x : A) (v : functional-tuple A n) (I : in-functional-tuple n x v) →
    x ＝ v (index-in-functional-tuple n x v I)
  eq-component-functional-tuple-index-in-functional-tuple n x v I = pr2 I
```

## Properties

### Characterizing equality of listed tuples

```agda
module _
  {l : Level} {A : UU l}
  where

  Eq-tuple : (n : ℕ) → tuple A n → tuple A n → UU l
  Eq-tuple zero-ℕ empty-tuple empty-tuple = raise-unit l
  Eq-tuple (succ-ℕ n) (x ∷ xs) (y ∷ ys) = (Id x y) × (Eq-tuple n xs ys)

  refl-Eq-tuple : (n : ℕ) → (u : tuple A n) → Eq-tuple n u u
  refl-Eq-tuple zero-ℕ empty-tuple = map-raise star
  pr1 (refl-Eq-tuple (succ-ℕ n) (x ∷ xs)) = refl
  pr2 (refl-Eq-tuple (succ-ℕ n) (x ∷ xs)) = refl-Eq-tuple n xs

  Eq-eq-tuple : (n : ℕ) → (u v : tuple A n) → Id u v → Eq-tuple n u v
  Eq-eq-tuple n u .u refl = refl-Eq-tuple n u

  eq-Eq-tuple : (n : ℕ) → (u v : tuple A n) → Eq-tuple n u v → Id u v
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
    (n : ℕ) (x : A) (u v : tuple A n) (p : Id u v) →
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

  extensionality-tuple : (n : ℕ) → (u v : tuple A n) → Id u v ≃ Eq-tuple n u v
  extensionality-tuple n u v = (Eq-eq-tuple n u v , is-equiv-Eq-eq-tuple n u v)
```

### The types of listed tuples and functional tuples are equivalent

```agda
module _
  {l : Level} {A : UU l}
  where

  listed-tuple-functional-tuple : (n : ℕ) → functional-tuple A n → tuple A n
  listed-tuple-functional-tuple zero-ℕ v = empty-tuple
  listed-tuple-functional-tuple (succ-ℕ n) v =
    head-functional-tuple n v ∷
    listed-tuple-functional-tuple n (tail-functional-tuple n v)

  functional-tuple-tuple : (n : ℕ) → tuple A n → functional-tuple A n
  functional-tuple-tuple zero-ℕ v = empty-functional-tuple
  functional-tuple-tuple (succ-ℕ n) (a ∷ v) =
    cons-functional-tuple n a (functional-tuple-tuple n v)

  is-section-functional-tuple-tuple :
    (n : ℕ) → (listed-tuple-functional-tuple n ∘ functional-tuple-tuple n) ~ id
  is-section-functional-tuple-tuple .zero-ℕ empty-tuple = refl
  is-section-functional-tuple-tuple .(succ-ℕ _) (a ∷ v) =
    ap (λ u → a ∷ u) (is-section-functional-tuple-tuple _ v)

  abstract
    is-retraction-functional-tuple-tuple :
      (n : ℕ) →
      (functional-tuple-tuple n ∘ listed-tuple-functional-tuple n) ~ id
    is-retraction-functional-tuple-tuple zero-ℕ v = eq-htpy (λ ())
    is-retraction-functional-tuple-tuple (succ-ℕ n) v =
      eq-htpy
        ( λ where
          ( inl x) →
            htpy-eq
              ( is-retraction-functional-tuple-tuple
                ( n)
                ( tail-functional-tuple n v))
              ( x)
          ( inr star) → refl)

  is-equiv-listed-tuple-functional-tuple :
    (n : ℕ) → is-equiv (listed-tuple-functional-tuple n)
  is-equiv-listed-tuple-functional-tuple n =
    is-equiv-is-invertible
      ( functional-tuple-tuple n)
      ( is-section-functional-tuple-tuple n)
      ( is-retraction-functional-tuple-tuple n)

  is-equiv-functional-tuple-tuple :
    (n : ℕ) → is-equiv (functional-tuple-tuple n)
  is-equiv-functional-tuple-tuple n =
    is-equiv-is-invertible
      ( listed-tuple-functional-tuple n)
      ( is-retraction-functional-tuple-tuple n)
      ( is-section-functional-tuple-tuple n)

  compute-tuple : (n : ℕ) → functional-tuple A n ≃ tuple A n
  pr1 (compute-tuple n) = listed-tuple-functional-tuple n
  pr2 (compute-tuple n) = is-equiv-listed-tuple-functional-tuple n
```

### Characterizing the elementhood predicate

```agda
  is-in-functional-tuple-is-in-tuple :
    (n : ℕ) (v : tuple A n) (x : A) →
    (x ∈-tuple v) → (in-functional-tuple n x (functional-tuple-tuple n v))
  is-in-functional-tuple-is-in-tuple (succ-ℕ n) (y ∷ l) x (is-head .x l) =
    (inr star) , refl
  is-in-functional-tuple-is-in-tuple
    (succ-ℕ n) (y ∷ l) x (is-in-tail .x x₁ l I) =
    inl (pr1 (is-in-functional-tuple-is-in-tuple n l x I)) ,
    pr2 (is-in-functional-tuple-is-in-tuple n l x I)

  is-in-tuple-is-in-functional-tuple :
    (n : ℕ) (v : tuple A n) (x : A) →
    (in-functional-tuple n x (functional-tuple-tuple n v)) → (x ∈-tuple v)
  is-in-tuple-is-in-functional-tuple (succ-ℕ n) (y ∷ v) x (inl k , p) =
    is-in-tail x y v (is-in-tuple-is-in-functional-tuple n v x (k , p))
  is-in-tuple-is-in-functional-tuple (succ-ℕ n) (y ∷ v) _ (inr k , refl) =
    is-head (functional-tuple-tuple (succ-ℕ n) (y ∷ v) (inr k)) v
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

#### The type of functional tuples of elements in a truncated type is truncated

```agda
module _
  {l : Level} {A : UU l}
  where

  is-trunc-functional-tuple :
    (k : 𝕋) (n : ℕ) → is-trunc k A → is-trunc k (functional-tuple A n)
  is-trunc-functional-tuple k n H = is-trunc-function-type k H
```

### The type of tuples of elements in a set is a set

#### The type of listed tuples of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-tuple : (n : ℕ) → is-set A -> is-set (tuple A n)
  is-set-tuple = is-trunc-tuple zero-𝕋

tuple-Set : {l : Level} → Set l → ℕ → Set l
pr1 (tuple-Set A n) = tuple (type-Set A) n
pr2 (tuple-Set A n) = is-set-tuple n (is-set-type-Set A)
```

#### The type of functional tuples of elements in a set is a set

```agda
module _
  {l : Level} {A : UU l}
  where

  is-set-functional-tuple : (n : ℕ) → is-set A → is-set (functional-tuple A n)
  is-set-functional-tuple = is-trunc-functional-tuple zero-𝕋

functional-tuple-Set : {l : Level} → Set l → ℕ → Set l
pr1 (functional-tuple-Set A n) = functional-tuple (type-Set A) n
pr2 (functional-tuple-Set A n) = is-set-functional-tuple n (is-set-type-Set A)
```

### Adding the tail to the head gives the same tuple

#### Adding the tail to the head gives the same listed tuple

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

#### Adding the tail to the head gives the same functional tuple

```agda
module _
  {l : Level} {A : UU l}
  where
  htpy-cons-head-tail-functional-tuple :
    ( n : ℕ) →
    ( v : functional-tuple A (succ-ℕ n)) →
    ( cons-functional-tuple n
      ( head-functional-tuple n v)
      ( tail-functional-tuple n v)) ~
      ( v)
  htpy-cons-head-tail-functional-tuple n v (inl x) = refl
  htpy-cons-head-tail-functional-tuple n v (inr star) = refl

  cons-head-tail-functional-tuple :
    ( n : ℕ) →
    ( v : functional-tuple A (succ-ℕ n)) →
    ( cons-functional-tuple n
      ( head-functional-tuple n v)
      ( tail-functional-tuple n v)) ＝
      ( v)
  cons-head-tail-functional-tuple n v =
    eq-htpy (htpy-cons-head-tail-functional-tuple n v)
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
