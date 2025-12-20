# Products of finite families of elements in commutative monoids

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.products-of-finite-families-of-elements-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
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
open import foundation.inhabited-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.products-of-finite-families-of-elements-commutative-semigroups
open import group-theory.products-of-finite-sequences-of-elements-commutative-monoids

open import univalent-combinatorics.complements-decidable-subtypes
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="of a finite family of elements of a commutative monoid" Agda=product-finite-Commutative-Monoid}}
extends the binary operation on a
[commutative monoid](group-theory.commutative-monoids.md) `M` to any family of
elements of `M` indexed by a
[finite type](univalent-combinatorics.finite-types.md).

## Products over counted types

### Definition

```agda
product-count-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2) →
  count A → (A → type-Commutative-Monoid M) → type-Commutative-Monoid M
product-count-Commutative-Monoid M A (n , Fin-n≃A) f =
  product-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv Fin-n≃A)
```

### Properties

#### Products for counts in a commutative monoid equal products in the corresponding commutative semigroup

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (A : UU l2) (|A| : is-inhabited A)
  where

  abstract
    eq-product-commutative-semigroup-product-count-Commutative-Monoid :
      (cA : count A) (f : A → type-Commutative-Monoid M) →
      product-count-Commutative-Monoid M A cA f ＝
      product-count-Commutative-Semigroup
        ( commutative-semigroup-Commutative-Monoid M)
        ( A)
        ( |A|)
        ( cA)
        ( f)
    eq-product-commutative-semigroup-product-count-Commutative-Monoid
      cA@(zero-ℕ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count cA refl))
    eq-product-commutative-semigroup-product-count-Commutative-Monoid
      cA@(succ-ℕ n , Fin-sn≃A) f =
      eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( n)
        ( f ∘ map-equiv Fin-sn≃A)
```

#### Products for a counted type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2)
  where

  abstract
    htpy-product-count-Commutative-Monoid :
      (c : count A) {f g : A → type-Commutative-Monoid M} → (f ~ g) →
      product-count-Commutative-Monoid M A c f ＝
      product-count-Commutative-Monoid M A c g
    htpy-product-count-Commutative-Monoid (nA , Fin-nA≃A) H =
      htpy-product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( nA)
        ( H ∘ map-equiv Fin-nA≃A)
```

#### Two counts for the same type produce equal products

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2)
  where

  abstract
    eq-product-count-Commutative-Monoid :
      (f : A → type-Commutative-Monoid M) (c1 c2 : count A) →
      product-count-Commutative-Monoid M A c1 f ＝
      product-count-Commutative-Monoid M A c2 f
    eq-product-count-Commutative-Monoid f c1@(zero-ℕ , _) c2@(_ , e2)
      with double-counting c1 c2
    ... | refl = refl
    eq-product-count-Commutative-Monoid f c1@(succ-ℕ n , e1) c2@(_ , e2)
      with double-counting c1 c2
    ... | refl =
      ( eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( n)
        ( f ∘ map-equiv e1)) ∙
      ( eq-product-count-Commutative-Semigroup
        ( commutative-semigroup-Commutative-Monoid M)
        ( A)
        ( unit-trunc-Prop (map-equiv e1 (inr star)))
        ( f)
        ( c1)
        ( c2)) ∙
      ( inv
        ( eq-product-commutative-semigroup-product-fin-sequence-type-Commutative-Monoid
          ( M)
          ( n)
          ( f ∘ map-equiv e2)))
```

#### Products of counted families indexed by equivalent types are equal

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : UU l2) (B : UU l3) (A≃B : A ≃ B)
  where

  abstract
    product-equiv-count-Commutative-Monoid :
      (cA : count A) (cB : count B) (f : A → type-Commutative-Monoid M) →
      product-count-Commutative-Monoid M A cA f ＝
      product-count-Commutative-Monoid M B cB (f ∘ map-inv-equiv A≃B)
    product-equiv-count-Commutative-Monoid
      cA@(nA , Fin-nA≃A) cB@(_ , Fin-nB≃B) f
      with double-counting-equiv cA cB A≃B
    ... | refl =
      ( preserves-product-permutation-fin-sequence-type-Commutative-Monoid
        ( M)
        ( nA)
        ( inv-equiv Fin-nA≃A ∘e inv-equiv A≃B ∘e Fin-nB≃B)
        ( _)) ∙
      ( htpy-product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( nA)
        ( λ i → ap f (is-section-map-inv-equiv Fin-nA≃A _)))
```

## Products over finite types

### Definition

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  opaque
    product-finite-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      type-Commutative-Monoid M
    product-finite-Commutative-Monoid f =
      map-universal-property-set-quotient-trunc-Prop
        ( set-Commutative-Monoid M)
        ( λ c → product-count-Commutative-Monoid M (type-Finite-Type A) c f)
        ( eq-product-count-Commutative-Monoid M (type-Finite-Type A) f)
        ( is-finite-type-Finite-Type A)
```

### Properties

#### The product over a finite type is its product over any count for the type

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (cA : count (type-Finite-Type A))
  where

  abstract opaque
    unfolding product-finite-Commutative-Monoid

    eq-product-finite-product-count-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      product-finite-Commutative-Monoid M A f ＝
      product-count-Commutative-Monoid M (type-Finite-Type A) cA f
    eq-product-finite-product-count-Commutative-Monoid f =
      equational-reasoning
        product-finite-Commutative-Monoid M A f
        ＝
          product-finite-Commutative-Monoid
            ( M)
            ( type-Finite-Type A , unit-trunc-Prop cA)
            ( f)
          by
            ap
              ( λ c →
                product-finite-Commutative-Monoid
                  ( M)
                  ( type-Finite-Type A , c)
                  ( f))
              ( all-elements-equal-type-trunc-Prop
                ( is-finite-type-Finite-Type A)
                ( unit-trunc-Prop cA))
        ＝ product-count-Commutative-Monoid M (type-Finite-Type A) cA f
          by
            htpy-universal-property-set-quotient-trunc-Prop
              ( set-Commutative-Monoid M)
              ( λ c →
                product-count-Commutative-Monoid M (type-Finite-Type A) c f)
              ( eq-product-count-Commutative-Monoid M (type-Finite-Type A) f)
              ( cA)
```

#### The product over an empty finite type is zero

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (¬A : is-empty (type-Finite-Type A))
  where

  abstract
    eq-unit-product-finite-is-empty-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      is-unit-Commutative-Monoid M (product-finite-Commutative-Monoid M A f)
    eq-unit-product-finite-is-empty-Commutative-Monoid =
      eq-product-finite-product-count-Commutative-Monoid M A (count-is-empty ¬A)
```

#### A product of units is the unit

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  abstract
    product-unit-finite-Commutative-Monoid :
      is-unit-Commutative-Monoid
        ( M)
        ( product-finite-Commutative-Monoid
          ( M)
          ( A)
          ( λ _ → unit-Commutative-Monoid M))
    product-unit-finite-Commutative-Monoid =
      let
        open
          do-syntax-trunc-Prop
            ( is-unit-prop-Commutative-Monoid
              ( M)
              ( product-finite-Commutative-Monoid
                ( M)
                ( A)
                ( λ _ → unit-Commutative-Monoid M)))
      in do
        cA ← is-finite-type-Finite-Type A
        ( ( eq-product-finite-product-count-Commutative-Monoid M A cA _) ∙
          ( product-unit-fin-sequence-type-Commutative-Monoid M _))
```

#### Products over a finite type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  abstract
    htpy-product-finite-Commutative-Monoid :
      {f g : type-Finite-Type A → type-Commutative-Monoid M} →
      f ~ g →
      product-finite-Commutative-Monoid M A f ＝
      product-finite-Commutative-Monoid M A g
    htpy-product-finite-Commutative-Monoid {f} {g} H =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( product-finite-Commutative-Monoid M A f)
              ( product-finite-Commutative-Monoid M A g))
      in do
        cA ← is-finite-type-Finite-Type A
        equational-reasoning
          product-finite-Commutative-Monoid M A f
          ＝ product-count-Commutative-Monoid M (type-Finite-Type A) cA f
            by eq-product-finite-product-count-Commutative-Monoid M A cA f
          ＝ product-count-Commutative-Monoid M (type-Finite-Type A) cA g
            by htpy-product-count-Commutative-Monoid M (type-Finite-Type A) cA H
          ＝ product-finite-Commutative-Monoid M A g
            by inv (eq-product-finite-product-count-Commutative-Monoid M A cA g)
```

#### Products over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  (H : equiv-Finite-Type A B)
  where

  abstract
    product-equiv-finite-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      product-finite-Commutative-Monoid M A f ＝
      product-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)
    product-equiv-finite-Commutative-Monoid f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( product-finite-Commutative-Monoid M A f)
              ( product-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)))
      in do
        cA ← is-finite-type-Finite-Type A
        cB ← is-finite-type-Finite-Type B
        equational-reasoning
          product-finite-Commutative-Monoid M A f
          ＝
            product-count-Commutative-Monoid M (type-Finite-Type A) cA f
            by eq-product-finite-product-count-Commutative-Monoid M A cA f
          ＝
            product-count-Commutative-Monoid
              ( M)
              ( type-Finite-Type B)
              ( cB)
              ( f ∘ map-inv-equiv H)
            by
              product-equiv-count-Commutative-Monoid
                ( M)
                ( type-Finite-Type A)
                ( type-Finite-Type B)
                ( H)
                ( cA)
                ( cB)
                ( f)
          ＝ product-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)
            by inv (eq-product-finite-product-count-Commutative-Monoid M B cB _)
```

#### Products over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  where

  abstract
    distributive-product-coproduct-finite-Commutative-Monoid :
      (f :
        type-Finite-Type A + type-Finite-Type B → type-Commutative-Monoid M) →
      product-finite-Commutative-Monoid M (coproduct-Finite-Type A B) f ＝
      mul-Commutative-Monoid
        ( M)
        ( product-finite-Commutative-Monoid M A (f ∘ inl))
        ( product-finite-Commutative-Monoid M B (f ∘ inr))
    distributive-product-coproduct-finite-Commutative-Monoid f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( product-finite-Commutative-Monoid
                ( M)
                ( coproduct-Finite-Type A B)
                ( f))
              ( mul-Commutative-Monoid
                ( M)
                ( product-finite-Commutative-Monoid M A (f ∘ inl))
                ( product-finite-Commutative-Monoid M B (f ∘ inr))))
      in do
        cA@(nA , Fin-nA≃A) ← is-finite-type-Finite-Type A
        cB@(nB , Fin-nB≃B) ← is-finite-type-Finite-Type B
        equational-reasoning
          product-finite-Commutative-Monoid M (coproduct-Finite-Type A B) f
          ＝
            product-fin-sequence-type-Commutative-Monoid
              ( M)
              ( nA +ℕ nB)
              ( f ∘ map-equiv-count (count-coproduct cA cB))
            by
              eq-product-finite-product-count-Commutative-Monoid
                ( M)
                ( coproduct-Finite-Type A B)
                ( count-coproduct cA cB)
                ( f)
          ＝
            mul-Commutative-Monoid M
              ( product-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nA)
                ( f ∘
                  map-equiv-count (count-coproduct cA cB) ∘
                  inl-coproduct-Fin nA nB))
              ( product-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nB)
                ( f ∘
                  map-equiv-count (count-coproduct cA cB) ∘
                  inr-coproduct-Fin nA nB))
            by
              split-product-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nA)
                ( nB)
                ( f ∘ map-equiv-count (count-coproduct cA cB))
          ＝
            mul-Commutative-Monoid
              ( M)
              ( product-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nA)
                ( f ∘ inl ∘ map-equiv-count cA))
              ( product-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nB)
                ( f ∘ inr ∘ map-equiv-count cB))
            by
              ap-mul-Commutative-Monoid
                ( M)
                ( ap
                  ( λ g →
                    product-fin-sequence-type-Commutative-Monoid M nA (f ∘ g))
                  ( eq-htpy
                    ( map-equiv-count-coproduct-inl-coproduct-Fin cA cB)))
                ( ap
                  ( λ g →
                    product-fin-sequence-type-Commutative-Monoid M nB (f ∘ g))
                  ( eq-htpy
                    ( map-equiv-count-coproduct-inr-coproduct-Fin cA cB)))
          ＝
            mul-Commutative-Monoid
              ( M)
              ( product-finite-Commutative-Monoid M A (f ∘ inl))
              ( product-finite-Commutative-Monoid M B (f ∘ inr))
            by
              inv
                ( ap-mul-Commutative-Monoid
                  ( M)
                  ( eq-product-finite-product-count-Commutative-Monoid
                    ( M)
                    ( A)
                    ( cA)
                    ( f ∘ inl))
                  ( eq-product-finite-product-count-Commutative-Monoid
                    ( M)
                    ( B)
                    ( cB)
                    ( f ∘ inr)))
```

#### Products distribute over dependent pair types

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    product-fin-finite-Σ-Commutative-Monoid :
      (n : ℕ) →
      {l2 : Level} →
      (B : Fin n → Finite-Type l2) →
      (f : (k : Fin n) → type-Finite-Type (B k) → type-Commutative-Monoid M) →
      product-fin-sequence-type-Commutative-Monoid M n
        (λ k → product-finite-Commutative-Monoid M (B k) (f k)) ＝
      product-finite-Commutative-Monoid
        M (Σ-Finite-Type (Fin-Finite-Type n) B) (ind-Σ f)
    product-fin-finite-Σ-Commutative-Monoid zero-ℕ B f =
      inv
        ( eq-unit-product-finite-is-empty-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type zero-ℕ) B)
          ( λ ())
          ( ind-Σ f))
    product-fin-finite-Σ-Commutative-Monoid (succ-ℕ n) B f =
      equational-reasoning
      product-fin-sequence-type-Commutative-Monoid
        ( M)
        ( succ-ℕ n)
        ( λ k → product-finite-Commutative-Monoid M (B k) (f k))
      ＝
        mul-Commutative-Monoid
          ( M)
          ( product-fin-sequence-type-Commutative-Monoid
            ( M)
            ( n)
            ( λ k →
              product-finite-Commutative-Monoid
                ( M)
                ( B (inl k))
                ( f (inl k))))
          ( product-finite-Commutative-Monoid
            ( M)
            ( B (inr star))
            ( f (inr star)))
        by
          cons-product-fin-sequence-type-Commutative-Monoid
            ( M)
            ( n)
            ( λ k → product-finite-Commutative-Monoid M (B k) (f k))
      ＝
        mul-Commutative-Monoid
          ( M)
          ( product-finite-Commutative-Monoid
            ( M)
            ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
            ( ind-Σ (f ∘ inl)))
          ( product-finite-Commutative-Monoid
            ( M)
            ( B (inr star))
            ( f (inr star)))
        by
          ap-mul-Commutative-Monoid
            ( M)
            ( product-fin-finite-Σ-Commutative-Monoid
              ( n)
              ( B ∘ inl)
              ( f ∘ inl))
            ( refl)
      ＝
        product-finite-Commutative-Monoid
          ( M)
          ( coproduct-Finite-Type
            ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
            ( B (inr star)))
          ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star)))
        by
          inv
            ( distributive-product-coproduct-finite-Commutative-Monoid
              ( M)
              ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
              ( B (inr star))
              ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star))))
      ＝
        product-finite-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
          ( ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star))) ∘
            ( map-coproduct
              ( id)
              ( map-left-unit-law-Σ (type-Finite-Type ∘ B ∘ inr))) ∘
            ( map-right-distributive-Σ-coproduct (type-Finite-Type ∘ B)))
        by
          product-equiv-finite-Commutative-Monoid
            ( M)
            ( coproduct-Finite-Type
              ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
              ( B (inr star)))
            ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
            ( inv-equiv
              ( ( equiv-coproduct
                  ( id-equiv)
                  ( left-unit-law-Σ (type-Finite-Type ∘ B ∘ inr))) ∘e
                ( right-distributive-Σ-coproduct (type-Finite-Type ∘ B))))
            ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star)))
      ＝
        product-finite-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
          ( ind-Σ f)
        by
          htpy-product-finite-Commutative-Monoid
            ( M)
            ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
            ( λ { (inl k , b) → refl ; (inr k , b) → refl})

module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  abstract
    product-Σ-finite-Commutative-Monoid :
      (f :
        (a : type-Finite-Type A) →
        type-Finite-Type (B a) →
        type-Commutative-Monoid M) →
      product-finite-Commutative-Monoid M (Σ-Finite-Type A B) (ind-Σ f) ＝
      product-finite-Commutative-Monoid
        ( M)
        ( A)
        ( λ a → product-finite-Commutative-Monoid M (B a) (f a))
    product-Σ-finite-Commutative-Monoid f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( product-finite-Commutative-Monoid
                ( M)
                ( Σ-Finite-Type A B)
                ( ind-Σ f))
              ( product-finite-Commutative-Monoid
                ( M)
                ( A)
                ( λ a → product-finite-Commutative-Monoid M (B a) (f a))))
      in do
        cA@(nA , Fin-nA≃A) ← is-finite-type-Finite-Type A
        equational-reasoning
          product-finite-Commutative-Monoid M (Σ-Finite-Type A B) (ind-Σ f)
          ＝
            product-finite-Commutative-Monoid
              ( M)
              ( Σ-Finite-Type (Fin-Finite-Type nA) (B ∘ map-equiv Fin-nA≃A))
              ( ind-Σ (f ∘ map-equiv Fin-nA≃A))
            by
              product-equiv-finite-Commutative-Monoid
                ( M)
                ( Σ-Finite-Type A B)
                ( Σ-Finite-Type (Fin-Finite-Type nA) (B ∘ map-equiv Fin-nA≃A))
                ( inv-equiv
                  ( equiv-Σ-equiv-base (type-Finite-Type ∘ B) Fin-nA≃A))
                ( ind-Σ f)
          ＝
            product-count-Commutative-Monoid
              ( M)
              ( type-Finite-Type A)
              ( cA)
              ( λ a → product-finite-Commutative-Monoid M (B a) (f a))
            by
              inv
                ( product-fin-finite-Σ-Commutative-Monoid
                  ( M)
                  ( nA)
                  ( B ∘ map-equiv Fin-nA≃A)
                  ( f ∘ map-equiv Fin-nA≃A))
          ＝
            product-finite-Commutative-Monoid
              ( M)
              ( A)
              ( λ a → product-finite-Commutative-Monoid M (B a) (f a))
            by inv (eq-product-finite-product-count-Commutative-Monoid M A cA _)
```

#### Products over the unit type

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    product-unit-finite-type-Commutative-Monoid :
      (f : unit → type-Commutative-Monoid M) →
      product-finite-Commutative-Monoid M unit-Finite-Type f ＝ f star
    product-unit-finite-type-Commutative-Monoid f =
      ( eq-product-finite-product-count-Commutative-Monoid
        ( M)
        ( unit-Finite-Type)
        ( count-unit)
        ( f)) ∙
      ( compute-product-one-element-Commutative-Monoid M _)
```

#### Products over contractible types

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (I : Finite-Type l2)
  (is-contr-I : is-contr (type-Finite-Type I))
  (i : type-Finite-Type I)
  where

  abstract
    product-finite-is-contr-Commutative-Monoid :
      (f : type-Finite-Type I → type-Commutative-Monoid M) →
      product-finite-Commutative-Monoid M I f ＝ f i
    product-finite-is-contr-Commutative-Monoid f =
      ( product-equiv-finite-Commutative-Monoid M
        ( I)
        ( unit-Finite-Type)
        ( equiv-unit-is-contr is-contr-I)
        ( f)) ∙
      ( product-unit-finite-type-Commutative-Monoid M _) ∙
      ( ap f (eq-is-contr is-contr-I))
```

#### Interchange law of products and addition

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  abstract
    interchange-product-mul-finite-Commutative-Monoid :
      (f g : type-Finite-Type A → type-Commutative-Monoid M) →
      product-finite-Commutative-Monoid M A
        ( λ a → mul-Commutative-Monoid M (f a) (g a)) ＝
      mul-Commutative-Monoid M
        ( product-finite-Commutative-Monoid M A f)
        ( product-finite-Commutative-Monoid M A g)
    interchange-product-mul-finite-Commutative-Monoid f g =
      equational-reasoning
      product-finite-Commutative-Monoid
        ( M)
        ( A)
        ( λ a → mul-Commutative-Monoid M (f a) (g a))
      ＝
        product-finite-Commutative-Monoid
          ( M)
          ( A)
          ( λ a → product-fin-sequence-type-Commutative-Monoid M 2 (h a))
          by
            htpy-product-finite-Commutative-Monoid
              ( M)
              ( A)
              ( λ a →
                inv (compute-product-two-elements-Commutative-Monoid M (h a)))
      ＝
        product-finite-Commutative-Monoid
          ( M)
          ( A)
          ( λ a → product-finite-Commutative-Monoid M (Fin-Finite-Type 2) (h a))
        by
          htpy-product-finite-Commutative-Monoid M A
            ( λ a →
              inv
                ( eq-product-finite-product-count-Commutative-Monoid
                  ( M)
                  ( Fin-Finite-Type 2)
                  ( count-Fin 2)
                  ( h a)))
      ＝
        product-finite-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type A (λ _ → Fin-Finite-Type 2))
          ( ind-Σ h)
        by
          inv
            ( product-Σ-finite-Commutative-Monoid
              ( M)
              ( A)
              ( λ _ → Fin-Finite-Type 2)
              ( h))
      ＝
        product-finite-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type 2) (λ _ → A))
          ( ind-Σ h')
        by
          product-equiv-finite-Commutative-Monoid M
            ( Σ-Finite-Type A (λ _ → Fin-Finite-Type 2))
            ( Σ-Finite-Type (Fin-Finite-Type 2) (λ _ → A))
            ( commutative-product)
            ( ind-Σ h)
      ＝
        product-finite-Commutative-Monoid
          ( M)
          ( Fin-Finite-Type 2)
          ( λ i → product-finite-Commutative-Monoid M A (h' i))
        by product-Σ-finite-Commutative-Monoid M _ _ _
      ＝
        product-fin-sequence-type-Commutative-Monoid
          ( M)
          ( 2)
          ( λ i → product-finite-Commutative-Monoid M A (h' i))
        by
          eq-product-finite-product-count-Commutative-Monoid
            ( M)
            ( Fin-Finite-Type 2)
            ( count-Fin 2)
            ( λ i → product-finite-Commutative-Monoid M A (h' i))
      ＝
        mul-Commutative-Monoid
          ( M)
          ( product-finite-Commutative-Monoid M A f)
          ( product-finite-Commutative-Monoid M A g)
        by
          compute-product-two-elements-Commutative-Monoid
            ( M)
            ( λ i → product-finite-Commutative-Monoid M A (h' i))
      where
        h : type-Finite-Type A → Fin 2 → type-Commutative-Monoid M
        h a (inl (inr _)) = f a
        h a (inr _) = g a
        h' : Fin 2 → type-Finite-Type A → type-Commutative-Monoid M
        h' i a = h a i
```

### Decomposing products via decidable subtypes

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  (P : subset-Finite-Type l3 A)
  where

  abstract opaque
    unfolding is-equiv-comp

    decompose-product-decidable-subset-finite-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      product-finite-Commutative-Monoid M A f ＝
      mul-Commutative-Monoid M
        ( product-finite-Commutative-Monoid M
          ( finite-type-subset-Finite-Type A P)
          ( f ∘ inclusion-subset-Finite-Type A P))
        ( product-finite-Commutative-Monoid M
          ( finite-type-complement-subset-Finite-Type A P)
          ( f ∘ inclusion-complement-subset-Finite-Type A P))
    decompose-product-decidable-subset-finite-Commutative-Monoid f =
      ( product-equiv-finite-Commutative-Monoid
        ( M)
        ( A)
        ( coproduct-Finite-Type
          ( finite-type-subset-Finite-Type A P)
          ( finite-type-complement-subset-Finite-Type A P))
        ( equiv-coproduct-decomposition-subset-Finite-Type A P)
        ( f)) ∙
      ( distributive-product-coproduct-finite-Commutative-Monoid
        ( M)
        ( finite-type-subset-Finite-Type A P)
        ( finite-type-complement-subset-Finite-Type A P)
        ( ( f) ∘
          ( map-inv-equiv
            ( equiv-coproduct-decomposition-subset-Finite-Type A P))))
```

### Products that vanish on a decidable subtype

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  (P : subset-Finite-Type l3 A)
  where

  abstract
    vanish-product-decidable-subset-finite-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      ( (a : type-Finite-Type A) → is-in-decidable-subtype P a →
        is-unit-Commutative-Monoid M (f a)) →
      product-finite-Commutative-Monoid M A f ＝
      product-finite-Commutative-Monoid M
        ( finite-type-complement-subset-Finite-Type A P)
        ( f ∘ inclusion-complement-subset-Finite-Type A P)
    vanish-product-decidable-subset-finite-Commutative-Monoid f H =
      ( decompose-product-decidable-subset-finite-Commutative-Monoid M A P f) ∙
      ( ap-mul-Commutative-Monoid M
        ( htpy-product-finite-Commutative-Monoid M _ (ind-Σ H) ∙
          product-unit-finite-Commutative-Monoid M _)
        ( refl)) ∙
      ( left-unit-law-mul-Commutative-Monoid M _)

    vanish-product-complement-decidable-subset-finite-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      ( (a : type-Finite-Type A) → ¬ (is-in-decidable-subtype P a) →
        is-unit-Commutative-Monoid M (f a)) →
      product-finite-Commutative-Monoid M A f ＝
      product-finite-Commutative-Monoid M
        ( finite-type-subset-Finite-Type A P)
        ( f ∘ inclusion-subset-Finite-Type A P)
    vanish-product-complement-decidable-subset-finite-Commutative-Monoid f H =
      ( decompose-product-decidable-subset-finite-Commutative-Monoid M A P f) ∙
      ( ap-mul-Commutative-Monoid M
        ( refl)
        ( htpy-product-finite-Commutative-Monoid M _ (ind-Σ H) ∙
          product-unit-finite-Commutative-Monoid M _)) ∙
      ( right-unit-law-mul-Commutative-Monoid M _)
```
