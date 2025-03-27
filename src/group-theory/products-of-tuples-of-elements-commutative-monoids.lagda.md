# Products of tuples of elements in commutative monoids

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.products-of-tuples-of-elements-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import group-theory.commutative-monoids
open import group-theory.monoids
open import group-theory.products-of-tuples-of-elements-monoids

open import linear-algebra.vectors-on-commutative-monoids

open import lists.lists

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The product operation extends the binary multiplication operation on a
[commutative monoid](group-theory.commutative-monoids.md) `M` to any family of
elements of `M` indexed by a
[standard finite type](univalent-combinatorics.standard-finite-types.md), or to
any [finite type](univalent-combinatorics.finite-types.md).

## Definition

```agda
mul-fin-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l) (n : ℕ) →
  (functional-vec-Commutative-Monoid M n) → type-Commutative-Monoid M
mul-fin-Commutative-Monoid M =
  mul-fin-Monoid (monoid-Commutative-Monoid M)
```

## Properties

### Products of one and two elements

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  mul-one-element-Commutative-Monoid :
    (f : functional-vec-Commutative-Monoid M 1) →
    mul-fin-Commutative-Monoid M 1 f ＝
    head-functional-vec-Commutative-Monoid M 0 f
  mul-one-element-Commutative-Monoid =
    mul-one-element-Monoid (monoid-Commutative-Monoid M)

  mul-two-elements-Commutative-Monoid :
    (f : functional-vec-Commutative-Monoid M 2) →
    mul-fin-Commutative-Monoid M 2 f ＝
    mul-Commutative-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))
  mul-two-elements-Commutative-Monoid =
    mul-two-elements-Monoid (monoid-Commutative-Monoid M)
```

### Products are homotopy invariant

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  htpy-mul-fin-Commutative-Monoid :
    (n : ℕ) {f g : functional-vec-Commutative-Monoid M n} →
    (f ~ g) →
    mul-fin-Commutative-Monoid M n f ＝ mul-fin-Commutative-Monoid M n g
  htpy-mul-fin-Commutative-Monoid =
    htpy-mul-fin-Monoid (monoid-Commutative-Monoid M)
```

### Products are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  cons-mul-fin-Commutative-Monoid :
    (n : ℕ) (f : functional-vec-Commutative-Monoid M (succ-ℕ n)) →
    {x : type-Commutative-Monoid M} →
    head-functional-vec-Commutative-Monoid M n f ＝ x →
    mul-fin-Commutative-Monoid M (succ-ℕ n) f ＝
    mul-Commutative-Monoid M (mul-fin-Commutative-Monoid M n (f ∘ inl-Fin n)) x
  cons-mul-fin-Commutative-Monoid =
    cons-mul-fin-Monoid (monoid-Commutative-Monoid M)

  snoc-mul-fin-Commutative-Monoid :
    (n : ℕ) (f : functional-vec-Commutative-Monoid M (succ-ℕ n)) →
    {x : type-Commutative-Monoid M} → f (zero-Fin n) ＝ x →
    mul-fin-Commutative-Monoid M (succ-ℕ n) f ＝
    mul-Commutative-Monoid M
      ( x)
      ( mul-fin-Commutative-Monoid M n (f ∘ inr-Fin n))
  snoc-mul-fin-Commutative-Monoid =
    snoc-mul-fin-Monoid (monoid-Commutative-Monoid M)
```

### Extending a product of elements in a monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  extend-mul-fin-Commutative-Monoid :
    (n : ℕ) (f : functional-vec-Commutative-Monoid M n) →
    mul-fin-Commutative-Monoid M
      ( succ-ℕ n)
      ( cons-functional-vec-Commutative-Monoid
        ( M)
        ( n)
        ( unit-Commutative-Monoid M) f) ＝
    mul-fin-Commutative-Monoid M n f
  extend-mul-fin-Commutative-Monoid =
    extend-mul-fin-Monoid (monoid-Commutative-Monoid M)
```

### Shifting a product of elements in a monoid

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  shift-mul-fin-Commutative-Monoid :
    (n : ℕ) (f : functional-vec-Commutative-Monoid M n) →
    mul-fin-Commutative-Monoid M
      ( succ-ℕ n)
      ( snoc-functional-vec-Commutative-Monoid M n f
        ( unit-Commutative-Monoid M)) ＝
    mul-fin-Commutative-Monoid M n f
  shift-mul-fin-Commutative-Monoid =
    shift-mul-fin-Monoid (monoid-Commutative-Monoid M)
```

### A product of units is the unit

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  mul-unit-Commutative-Monoid :
    (n : ℕ) →
    mul-fin-Commutative-Monoid
      ( M)
      ( n)
      ( unit-functional-vec-Commutative-Monoid M n) ＝
    unit-Commutative-Monoid M
  mul-unit-Commutative-Monoid =
    mul-unit-Monoid (monoid-Commutative-Monoid M)
```

### Splitting products

```agda
split-mul-fin-Commutative-Monoid :
  {l : Level} (M : Commutative-Monoid l)
  (n m : ℕ) (f : functional-vec-Commutative-Monoid M (n +ℕ m)) →
  mul-fin-Commutative-Monoid M (n +ℕ m) f ＝
  mul-Commutative-Monoid M
    ( mul-fin-Commutative-Monoid M n (f ∘ inl-coproduct-Fin n m))
    ( mul-fin-Commutative-Monoid M m (f ∘ inr-coproduct-Fin n m))
split-mul-fin-Commutative-Monoid M =
  split-mul-fin-Monoid (monoid-Commutative-Monoid M)
```

### Permutations preserve products

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    preserves-product-adjacent-transposition-mul-fin-Commutative-Monoid :
      (n : ℕ) → (k : Fin n) →
      (f : functional-vec-Commutative-Monoid M (succ-ℕ n)) →
      mul-fin-Commutative-Monoid M (succ-ℕ n) f ＝
      mul-fin-Commutative-Monoid
        M (succ-ℕ n) (f ∘ map-adjacent-transposition-Fin n k)
    preserves-product-adjacent-transposition-mul-fin-Commutative-Monoid
      (succ-ℕ n) (inl x) f =
        ap-mul-Commutative-Monoid
          ( M)
          ( preserves-product-adjacent-transposition-mul-fin-Commutative-Monoid
            ( n)
            ( x)
            ( f ∘ inl-Fin (succ-ℕ n)))
          ( refl)
    preserves-product-adjacent-transposition-mul-fin-Commutative-Monoid
      (succ-ℕ n) (inr star) f = right-swap-mul-Commutative-Monoid M _ _ _

    preserves-product-permutation-list-adjacent-transpositions-Commutative-Monoid :
      (n : ℕ) → (L : list (Fin n)) →
      (f : functional-vec-Commutative-Monoid M (succ-ℕ n)) →
      mul-fin-Commutative-Monoid M (succ-ℕ n) f ＝
      mul-fin-Commutative-Monoid
        M (succ-ℕ n) (f ∘ map-permutation-list-adjacent-transpositions n L)
    preserves-product-permutation-list-adjacent-transpositions-Commutative-Monoid
      n nil f = refl
    preserves-product-permutation-list-adjacent-transpositions-Commutative-Monoid
      n (cons x L) f =
        preserves-product-adjacent-transposition-mul-fin-Commutative-Monoid
          ( n)
          ( x)
          ( f) ∙
        preserves-product-permutation-list-adjacent-transpositions-Commutative-Monoid
          ( n)
          ( L)
          ( f ∘ map-adjacent-transposition-Fin n x)

    preserves-product-transposition-Commutative-Monoid :
      (n : ℕ) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
      (f : functional-vec-Commutative-Monoid M (succ-ℕ n)) →
      mul-fin-Commutative-Monoid M (succ-ℕ n) f ＝
      mul-fin-Commutative-Monoid
        M (succ-ℕ n) (f ∘ map-transposition-Fin (succ-ℕ n) i j neq)
    preserves-product-transposition-Commutative-Monoid n i j i≠j f =
      preserves-product-permutation-list-adjacent-transpositions-Commutative-Monoid
        ( n)
        ( list-adjacent-transpositions-transposition-Fin n i j)
        ( f) ∙
      ap
        ( λ g → mul-fin-Commutative-Monoid M (succ-ℕ n) (f ∘ map-equiv g))
        ( eq-permutation-list-adjacent-transpositions-transposition-Fin
          ( n)
          ( i)
          ( j)
          ( i≠j))

    preserves-product-permutation-list-standard-transpositions-Commutative-Monoid :
      (n : ℕ) → (L : list (Σ (Fin n × Fin n) ( λ (i , j) → i ≠ j))) →
      (f : functional-vec-Commutative-Monoid M n) →
      mul-fin-Commutative-Monoid M n f ＝
      mul-fin-Commutative-Monoid
        M n (f ∘ map-equiv (permutation-list-standard-transpositions-Fin n L))
    preserves-product-permutation-list-standard-transpositions-Commutative-Monoid
      zero-ℕ _ _ = refl
    preserves-product-permutation-list-standard-transpositions-Commutative-Monoid
      (succ-ℕ n) nil f = refl
    preserves-product-permutation-list-standard-transpositions-Commutative-Monoid
      (succ-ℕ n) (cons ((i , j) , i≠j) L) f =
        preserves-product-transposition-Commutative-Monoid n i j i≠j f ∙
        preserves-product-permutation-list-standard-transpositions-Commutative-Monoid
          ( succ-ℕ n)
          ( L)
          ( f ∘ map-transposition-Fin (succ-ℕ n) i j i≠j)

    preserves-product-permutation-Commutative-Monoid :
      (n : ℕ) → (σ : Permutation n) →
      (f : functional-vec-Commutative-Monoid M n) →
      mul-fin-Commutative-Monoid M n f ＝
      mul-fin-Commutative-Monoid M n (f ∘ map-equiv σ)
    preserves-product-permutation-Commutative-Monoid n σ f =
      preserves-product-permutation-list-standard-transpositions-Commutative-Monoid
        ( n)
        ( list-standard-transpositions-permutation-Fin n σ)
        ( f) ∙
      ap
        ( λ τ → mul-fin-Commutative-Monoid M n (f ∘ map-equiv τ))
        ( eq-permutation-list-standard-transpositions-Fin n σ)
```

### Products for a count for a type

```agda
mul-count-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2) →
  count A → (A → type-Commutative-Monoid M) → type-Commutative-Monoid M
mul-count-Commutative-Monoid M A (n , Fin-n≃A) f =
  mul-fin-Commutative-Monoid M n (f ∘ map-equiv Fin-n≃A)
```

### Products for a count for a type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2)
  where

  htpy-mul-count-Commutative-Monoid :
    (c : count A) →
    {f g : A → type-Commutative-Monoid M} → (f ~ g) →
    mul-count-Commutative-Monoid M A c f ＝
    mul-count-Commutative-Monoid M A c g
  htpy-mul-count-Commutative-Monoid (nA , _) H =
    htpy-mul-fin-Commutative-Monoid M nA (λ i → H _)
```

### Two counts for the same set produce equal products

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2)
  where

  abstract
    eq-mul-count-equiv-Commutative-Monoid :
      (n : ℕ) → (equiv1 equiv2 : Fin n ≃ A) →
      (f : A → type-Commutative-Monoid M) →
      mul-count-Commutative-Monoid M A (n , equiv1) f ＝
      mul-count-Commutative-Monoid M A (n , equiv2) f
    eq-mul-count-equiv-Commutative-Monoid n equiv1 equiv2 f =
      equational-reasoning
      mul-fin-Commutative-Monoid M n (f ∘ map-equiv equiv1)
      ＝
        mul-fin-Commutative-Monoid
          ( M)
          ( n)
          ( (f ∘ map-equiv equiv1) ∘ (map-inv-equiv equiv1 ∘ map-equiv equiv2))
        by
          preserves-product-permutation-Commutative-Monoid
            ( M)
            ( n)
            ( inv-equiv equiv1 ∘e equiv2)
            ( f ∘ map-equiv equiv1)
      ＝ mul-fin-Commutative-Monoid M n (f ∘ map-equiv equiv2)
        by
          ap
            ( λ g → mul-fin-Commutative-Monoid M n (f ∘ (g ∘ map-equiv equiv2)))
            ( eq-htpy (is-section-map-inv-equiv equiv1))

    eq-mul-count-Commutative-Monoid :
      (f : A → type-Commutative-Monoid M) (c1 c2 : count A) →
      mul-count-Commutative-Monoid M A c1 f ＝
      mul-count-Commutative-Monoid M A c2 f
    eq-mul-count-Commutative-Monoid f c1@(n , e1) c2@(_ , e2)
      with double-counting c1 c2
    ... | refl = eq-mul-count-equiv-Commutative-Monoid n e1 e2 f
```

### Products over finite types

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  mul-finite-Commutative-Monoid :
    (f : type-Finite-Type A → type-Commutative-Monoid M) →
    type-Commutative-Monoid M
  mul-finite-Commutative-Monoid f =
    map-universal-property-set-quotient-trunc-Prop
      ( set-Commutative-Monoid M)
      ( λ c → mul-count-Commutative-Monoid M (type-Finite-Type A) c f)
      ( eq-mul-count-Commutative-Monoid M (type-Finite-Type A) f)
      ( is-finite-type-Finite-Type A)
```

### The product over a finite type is its product over any count for the type

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : UU l2) (B : UU l3) (H : A ≃ B)
  where

  abstract
    mul-equiv-count-Commutative-Monoid :
      (cA : count A) (cB : count B) (f : A → type-Commutative-Monoid M) →
      mul-count-Commutative-Monoid M A cA f ＝
      mul-count-Commutative-Monoid M B cB (f ∘ map-inv-equiv H)
    mul-equiv-count-Commutative-Monoid
      cA@(nA , Fin-nA≃A) cB@(_ , Fin-nB≃B) f
      with double-counting-equiv cA cB H
    ... | refl =
      preserves-product-permutation-Commutative-Monoid
        ( M)
        ( nA)
        ( inv-equiv Fin-nA≃A ∘e inv-equiv H ∘e Fin-nB≃B)
        ( _) ∙
      htpy-mul-fin-Commutative-Monoid
        ( M)
        ( nA)
        ( λ i → ap f (is-section-map-inv-equiv Fin-nA≃A _))

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (cA : count (type-Finite-Type A))
  where

  abstract
    mul-finite-count-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      mul-finite-Commutative-Monoid M A f ＝
      mul-count-Commutative-Monoid M (type-Finite-Type A) cA f
    mul-finite-count-Commutative-Monoid f =
      equational-reasoning
        mul-finite-Commutative-Monoid M A f
        ＝
          mul-finite-Commutative-Monoid
            ( M)
            ( type-Finite-Type A , unit-trunc-Prop cA)
            ( f)
          by
            ap
              ( λ c →
                mul-finite-Commutative-Monoid
                  ( M)
                  ( type-Finite-Type A , c)
                  ( f))
              ( all-elements-equal-type-trunc-Prop
                ( is-finite-type-Finite-Type A)
                ( unit-trunc-Prop cA))
        ＝ mul-count-Commutative-Monoid M (type-Finite-Type A) cA f
          by
            htpy-universal-property-set-quotient-trunc-Prop
              ( set-Commutative-Monoid M)
              ( λ c →
                mul-count-Commutative-Monoid M (type-Finite-Type A) c f)
              ( eq-mul-count-Commutative-Monoid M (type-Finite-Type A) f)
              ( cA)
```

### The product over an empty type is the unit

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  abstract
    mul-is-empty-finite-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      is-unit-Commutative-Monoid M (mul-finite-Commutative-Monoid M A f)
    mul-is-empty-finite-Commutative-Monoid =
      mul-finite-count-Commutative-Monoid M A (count-is-empty H)
```

### The product of units is the unit

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  mul-unit-finite-Commutative-Monoid :
    is-unit-Commutative-Monoid
      ( M)
      ( mul-finite-Commutative-Monoid
        ( M)
        ( A)
        ( λ _ → unit-Commutative-Monoid M))
  mul-unit-finite-Commutative-Monoid =
    do
      cA ← is-finite-type-Finite-Type A
      equational-reasoning
        mul-finite-Commutative-Monoid M A (λ _ → unit-Commutative-Monoid M)
        ＝
          mul-count-Commutative-Monoid
            ( M)
            ( type-Finite-Type A)
            ( cA)
            ( λ _ → unit-Commutative-Monoid M)
          by mul-finite-count-Commutative-Monoid M A cA _
        ＝ unit-Commutative-Monoid M by mul-unit-Commutative-Monoid M _
    where
      open
        do-syntax-trunc-Prop
          (is-unit-prop-Commutative-Monoid
            ( M)
            ( mul-finite-Commutative-Monoid
              ( M)
              ( A)
              ( λ _ → unit-Commutative-Monoid M)))
```

### Products over a finite type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  abstract
    htpy-mul-finite-Commutative-Monoid :
      {f g : type-Finite-Type A → type-Commutative-Monoid M} →
      f ~ g →
      mul-finite-Commutative-Monoid M A f ＝ mul-finite-Commutative-Monoid M A g
    htpy-mul-finite-Commutative-Monoid {f} {g} H =
      do
        cA ← is-finite-type-Finite-Type A
        equational-reasoning
          mul-finite-Commutative-Monoid M A f
          ＝ mul-count-Commutative-Monoid M (type-Finite-Type A) cA f
            by mul-finite-count-Commutative-Monoid M A cA f
          ＝ mul-count-Commutative-Monoid M (type-Finite-Type A) cA g
            by htpy-mul-count-Commutative-Monoid M (type-Finite-Type A) cA H
          ＝ mul-finite-Commutative-Monoid M A g
            by inv (mul-finite-count-Commutative-Monoid M A cA g)
      where
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( mul-finite-Commutative-Monoid M A f)
              ( mul-finite-Commutative-Monoid M A g))
```

### Products over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  (H : equiv-Finite-Type A B)
  where

  abstract
    mul-equiv-finite-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      mul-finite-Commutative-Monoid M A f ＝
      mul-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)
    mul-equiv-finite-Commutative-Monoid f =
      do
        cA ← is-finite-type-Finite-Type A
        cB ← is-finite-type-Finite-Type B
        equational-reasoning
          mul-finite-Commutative-Monoid M A f
          ＝
            mul-count-Commutative-Monoid M (type-Finite-Type A) cA f
            by mul-finite-count-Commutative-Monoid M A cA f
          ＝
            mul-count-Commutative-Monoid
              ( M)
              ( type-Finite-Type B)
              ( cB)
              ( f ∘ map-inv-equiv H)
            by
              mul-equiv-count-Commutative-Monoid
                ( M)
                ( type-Finite-Type A)
                ( type-Finite-Type B)
                ( H)
                ( cA)
                ( cB)
                ( f)
          ＝ mul-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)
            by inv (mul-finite-count-Commutative-Monoid M B cB _)
      where
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( mul-finite-Commutative-Monoid M A f)
              ( mul-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)))
```

### Products over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  where

  abstract
    mul-coproduct-finite-Commutative-Monoid :
      (f :
        type-Finite-Type A + type-Finite-Type B → type-Commutative-Monoid M) →
      mul-finite-Commutative-Monoid M (coproduct-Finite-Type A B) f ＝
      mul-Commutative-Monoid
        ( M)
        ( mul-finite-Commutative-Monoid M A (f ∘ inl))
        ( mul-finite-Commutative-Monoid M B (f ∘ inr))
    mul-coproduct-finite-Commutative-Monoid f =
      do
        cA@(nA , Fin-nA≃A) ← is-finite-type-Finite-Type A
        cB@(nB , Fin-nB≃B) ← is-finite-type-Finite-Type B
        equational-reasoning
          mul-finite-Commutative-Monoid M (coproduct-Finite-Type A B) f
          ＝
            mul-fin-Commutative-Monoid
              ( M)
              ( nA +ℕ nB)
              ( f ∘ map-equiv-count (count-coproduct cA cB))
            by
              mul-finite-count-Commutative-Monoid
                ( M)
                ( coproduct-Finite-Type A B)
                ( count-coproduct cA cB)
                ( f)
          ＝
            mul-Commutative-Monoid M
              ( mul-fin-Commutative-Monoid
                ( M)
                ( nA)
                ( f ∘
                  map-equiv-count (count-coproduct cA cB) ∘
                  inl-coproduct-Fin nA nB))
              ( mul-fin-Commutative-Monoid
                ( M)
                ( nB)
                ( f ∘
                  map-equiv-count (count-coproduct cA cB) ∘
                  inr-coproduct-Fin nA nB))
            by
              split-mul-fin-Commutative-Monoid
                ( M)
                ( nA)
                ( nB)
                ( f ∘ map-equiv-count (count-coproduct cA cB))
          ＝
            mul-Commutative-Monoid
              ( M)
              ( mul-fin-Commutative-Monoid
                ( M)
                ( nA)
                ( f ∘ inl ∘ map-equiv-count cA))
              ( mul-fin-Commutative-Monoid
                ( M)
                ( nB)
                ( f ∘ inr ∘ map-equiv-count cB))
            by
              ap-mul-Commutative-Monoid
                ( M)
                ( ap
                  ( λ g → mul-fin-Commutative-Monoid M nA (f ∘ g))
                  ( eq-htpy
                    ( map-equiv-count-coproduct-inl-coproduct-Fin cA cB)))
                ( ap
                  ( λ g → mul-fin-Commutative-Monoid M nB (f ∘ g))
                  ( eq-htpy
                    ( map-equiv-count-coproduct-inr-coproduct-Fin cA cB)))
          ＝
            mul-Commutative-Monoid
              ( M)
              ( mul-finite-Commutative-Monoid M A (f ∘ inl))
              ( mul-finite-Commutative-Monoid M B (f ∘ inr))
            by
              inv
                ( ap-mul-Commutative-Monoid
                  ( M)
                  ( mul-finite-count-Commutative-Monoid
                    ( M)
                    ( A)
                    ( cA)
                    ( f ∘ inl))
                  ( mul-finite-count-Commutative-Monoid
                    ( M)
                    ( B)
                    ( cB)
                    ( f ∘ inr)))
      where
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( mul-finite-Commutative-Monoid
                ( M)
                ( coproduct-Finite-Type A B)
                ( f))
              ( mul-Commutative-Monoid
                ( M)
                ( mul-finite-Commutative-Monoid M A (f ∘ inl))
                ( mul-finite-Commutative-Monoid M B (f ∘ inr))))
```

### Products distribute over dependent pair types

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    mul-fin-finite-Σ-Commutative-Monoid :
      (n : ℕ) →
      {l2 : Level} →
      (B : Fin n → Finite-Type l2) →
      (f : (k : Fin n) → type-Finite-Type (B k) → type-Commutative-Monoid M) →
      mul-fin-Commutative-Monoid M n
        (λ k → mul-finite-Commutative-Monoid M (B k) (f k)) ＝
      mul-finite-Commutative-Monoid
        M (Σ-Finite-Type (Fin-Finite-Type n) B) (ind-Σ f)
    mul-fin-finite-Σ-Commutative-Monoid zero-ℕ B f =
      inv
        ( mul-is-empty-finite-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type zero-ℕ) B)
          ( λ ())
          ( ind-Σ f))
    mul-fin-finite-Σ-Commutative-Monoid (succ-ℕ n) B f = equational-reasoning
      mul-fin-Commutative-Monoid
        ( M)
        ( succ-ℕ n)
        ( λ k → mul-finite-Commutative-Monoid M (B k) (f k))
      ＝
        mul-Commutative-Monoid
          ( M)
          ( mul-fin-Commutative-Monoid
            ( M)
            ( n)
            ( λ k →
              mul-finite-Commutative-Monoid
                ( M)
                ( B (inl k))
                ( f (inl k))))
          ( mul-finite-Commutative-Monoid
            ( M)
            ( B (inr star))
            ( f (inr star)))
        by
          cons-mul-fin-Commutative-Monoid
            ( M)
            ( n)
            ( λ k → mul-finite-Commutative-Monoid M (B k) (f k))
            ( refl)
      ＝
        mul-Commutative-Monoid
          ( M)
          ( mul-finite-Commutative-Monoid
            ( M)
            ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
            ( ind-Σ (f ∘ inl)))
          ( mul-finite-Commutative-Monoid
            ( M)
            ( B (inr star))
            ( f (inr star)))
        by
          ap-mul-Commutative-Monoid
            ( M)
            ( mul-fin-finite-Σ-Commutative-Monoid
              ( n)
              ( B ∘ inl)
              ( f ∘ inl))
            ( refl)
      ＝
        mul-finite-Commutative-Monoid
          ( M)
          ( coproduct-Finite-Type
            ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
            ( B (inr star)))
          ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star)))
        by
          inv
            ( mul-coproduct-finite-Commutative-Monoid
              ( M)
              ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
              ( B (inr star))
              ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star))))
      ＝
        mul-finite-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
          ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star)) ∘
            map-coproduct
              ( id)
              ( map-left-unit-law-Σ (type-Finite-Type ∘ B ∘ inr)) ∘
            map-right-distributive-Σ-coproduct
              ( Fin n)
              ( unit)
              ( type-Finite-Type ∘ B))
        by
          mul-equiv-finite-Commutative-Monoid
            ( M)
            ( coproduct-Finite-Type
              ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
              ( B (inr star)))
            (Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
            ( inv-equiv
              ( equiv-coproduct
                ( id-equiv)
                ( left-unit-law-Σ (type-Finite-Type ∘ B ∘ inr)) ∘e
                right-distributive-Σ-coproduct
                  ( Fin n)
                  ( unit)
                  ( type-Finite-Type ∘ B)))
            _
      ＝
        mul-finite-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
          ( ind-Σ f)
        by
          htpy-mul-finite-Commutative-Monoid
            ( M)
            ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
            ( λ { (inl k , b) → refl ; (inr k , b) → refl})

module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  abstract
    mul-Σ-finite-Commutative-Monoid :
      (f :
        (a : type-Finite-Type A) →
        type-Finite-Type (B a) →
        type-Commutative-Monoid M) →
      mul-finite-Commutative-Monoid M (Σ-Finite-Type A B) (ind-Σ f) ＝
      mul-finite-Commutative-Monoid
        ( M)
        ( A)
        ( λ a → mul-finite-Commutative-Monoid M (B a) (f a))
    mul-Σ-finite-Commutative-Monoid f =
      do
        cA@(nA , Fin-nA≃A) ← is-finite-type-Finite-Type A
        equational-reasoning
          mul-finite-Commutative-Monoid M (Σ-Finite-Type A B) (ind-Σ f)
          ＝
            mul-finite-Commutative-Monoid
              ( M)
              ( Σ-Finite-Type (Fin-Finite-Type nA) (B ∘ map-equiv Fin-nA≃A))
              ( ind-Σ (f ∘ map-equiv Fin-nA≃A))
            by
              mul-equiv-finite-Commutative-Monoid
                ( M)
                ( Σ-Finite-Type A B)
                ( Σ-Finite-Type (Fin-Finite-Type nA) (B ∘ map-equiv Fin-nA≃A))
                ( inv-equiv
                  ( equiv-Σ-equiv-base (type-Finite-Type ∘ B) Fin-nA≃A))
                ( _)
          ＝
            mul-count-Commutative-Monoid
              ( M)
              ( type-Finite-Type A)
              ( cA)
              ( λ a → mul-finite-Commutative-Monoid M (B a) (f a))
            by
              inv
                ( mul-fin-finite-Σ-Commutative-Monoid
                  ( M)
                  ( nA)
                  ( B ∘ map-equiv Fin-nA≃A)
                  ( f ∘ map-equiv Fin-nA≃A))
          ＝
            mul-finite-Commutative-Monoid
              ( M)
              ( A)
              ( λ a → mul-finite-Commutative-Monoid M (B a) (f a))
            by inv (mul-finite-count-Commutative-Monoid M A cA _)
      where
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( mul-finite-Commutative-Monoid M (Σ-Finite-Type A B) (ind-Σ f))
              ( mul-finite-Commutative-Monoid
                ( M)
                ( A)
                ( λ a → mul-finite-Commutative-Monoid M (B a) (f a))))
```

### Products over the unit type

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    mul-finite-unit-Commutative-Monoid :
      (f : unit → type-Commutative-Monoid M) →
      mul-finite-Commutative-Monoid M unit-Finite-Type f ＝ f star
    mul-finite-unit-Commutative-Monoid f =
      equational-reasoning
        mul-finite-Commutative-Monoid M unit-Finite-Type f
        ＝
          mul-count-Commutative-Monoid
            ( M)
            ( unit)
            ( count-unit)
            ( f)
          by
            mul-finite-count-Commutative-Monoid
              ( M)
              ( unit-Finite-Type)
              ( count-unit)
              ( f)
        ＝ f star by mul-one-element-Commutative-Monoid M _
```
