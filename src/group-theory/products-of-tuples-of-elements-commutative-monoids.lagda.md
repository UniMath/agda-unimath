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
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.propositional-truncations
open import foundation.sets
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

  product-one-element-Commutative-Monoid :
    (f : functional-vec-Commutative-Monoid M 1) →
    mul-fin-Commutative-Monoid M 1 f ＝
    head-functional-vec-Commutative-Monoid M 0 f
  product-one-element-Commutative-Monoid =
    product-one-element-Monoid (monoid-Commutative-Monoid M)

  product-two-elements-Commutative-Monoid :
    (f : functional-vec-Commutative-Monoid M 2) →
    mul-fin-Commutative-Monoid M 2 f ＝
    mul-Commutative-Monoid M (f (zero-Fin 1)) (f (one-Fin 1))
  product-two-elements-Commutative-Monoid =
    product-two-elements-Monoid (monoid-Commutative-Monoid M)
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

  product-unit-Commutative-Monoid :
    (n : ℕ) →
    mul-fin-Commutative-Monoid
      ( M)
      ( n)
      ( unit-functional-vec-Commutative-Monoid M n) ＝
    unit-Commutative-Monoid M
  product-unit-Commutative-Monoid =
    product-unit-Monoid (monoid-Commutative-Monoid M)
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
      ＝
        mul-fin-Commutative-Monoid
          ( M)
          ( n)
          ( f ∘ (map-equiv equiv1 ∘ (map-inv-equiv equiv1 ∘ map-equiv equiv2)))
        by
          ap
            ( mul-fin-Commutative-Monoid M n)
            ( associative-comp f (map-equiv equiv1) _)
      ＝
        mul-fin-Commutative-Monoid
          ( M)
          ( n)
          ( f ∘ ((map-equiv equiv1 ∘ map-inv-equiv equiv1) ∘ map-equiv equiv2))
        by
          ap
            ( λ g → mul-fin-Commutative-Monoid M n (f ∘ g))
            ( inv
              ( associative-comp (map-equiv equiv1) (map-inv-equiv equiv1) _))
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
      with eq-number-of-elements-count A c1 c2
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
    product-equiv-count-Commutative-Monoid :
      (cA : count A) (cB : count B) (f : B → type-Commutative-Monoid M) →
      mul-count-Commutative-Monoid M B cB f ＝
      mul-count-Commutative-Monoid M A cA (f ∘ map-equiv H)
    product-equiv-count-Commutative-Monoid
      cA@(_ , Fin-nA≃A) cB@(nB , Fin-nB≃B) f
      with eq-number-of-elements-count-equiv A B H cA cB
    ... | refl =
      preserves-product-permutation-Commutative-Monoid
        ( M)
        ( nB)
        ( inv-equiv Fin-nB≃B ∘e H ∘e Fin-nA≃A)
        ( f ∘ map-equiv Fin-nB≃B) ∙
      ap
        ( λ g →
          mul-fin-Commutative-Monoid
            ( M)
            ( nB)
            ((f ∘ g) ∘ (map-equiv (H ∘e Fin-nA≃A))))
        ( eq-htpy (is-section-map-inv-equiv Fin-nB≃B))

module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (cA : count (type-Finite-Type A))
  where

  abstract
    eq-product-finite-count-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      mul-finite-Commutative-Monoid M A f ＝
      mul-count-Commutative-Monoid M (type-Finite-Type A) cA f
    eq-product-finite-count-Commutative-Monoid f =
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
            by eq-product-finite-count-Commutative-Monoid M A cA f
          ＝ mul-count-Commutative-Monoid M (type-Finite-Type A) cA g
            by htpy-mul-count-Commutative-Monoid M (type-Finite-Type A) cA H
          ＝ mul-finite-Commutative-Monoid M A g
            by inv (eq-product-finite-count-Commutative-Monoid M A cA g)
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
    product-equiv-finite-Commutative-Monoid :
      (f : type-Finite-Type B → type-Commutative-Monoid M) →
      mul-finite-Commutative-Monoid M B f ＝
      mul-finite-Commutative-Monoid M A (f ∘ map-equiv H)
    product-equiv-finite-Commutative-Monoid f =
      do
        cA ← is-finite-type-Finite-Type A
        cB ← is-finite-type-Finite-Type B
        equational-reasoning
          mul-finite-Commutative-Monoid M B f
          ＝ mul-count-Commutative-Monoid M (type-Finite-Type B) cB f
            by eq-product-finite-count-Commutative-Monoid M B cB f
          ＝
            mul-count-Commutative-Monoid
              ( M)
              ( type-Finite-Type A)
              ( cA)
              ( f ∘ map-equiv H)
            by
              product-equiv-count-Commutative-Monoid
                ( M)
                ( type-Finite-Type A)
                ( type-Finite-Type B)
                ( H)
                ( cA)
                ( cB)
                ( f)
          ＝ mul-finite-Commutative-Monoid M A (f ∘ map-equiv H)
            by
              inv
                ( eq-product-finite-count-Commutative-Monoid
                  ( M)
                  ( A)
                  ( cA)
                  ( f ∘ map-equiv H))
      where
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( mul-finite-Commutative-Monoid M B f)
              ( mul-finite-Commutative-Monoid M A (f ∘ map-equiv H)))
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
              eq-product-finite-count-Commutative-Monoid
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
                  ( eq-product-finite-count-Commutative-Monoid
                    ( M)
                    ( A)
                    ( cA)
                    ( f ∘ inl))
                  ( eq-product-finite-count-Commutative-Monoid
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
