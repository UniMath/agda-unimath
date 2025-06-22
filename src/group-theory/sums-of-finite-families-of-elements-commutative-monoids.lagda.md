# Sums of finite families of elements in commutative monoids

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.sums-of-finite-families-of-elements-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
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
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.sums-of-finite-sequences-of-elements-commutative-monoids

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

The
{{#concept "sum operation" Disambiguation="of a finite family of elements of a commutative monoid" WD="sum" WDID=Q218005 Agda=sum-finite-Commutative-Monoid}}
extends the binary operation on a
[commutative monoid](group-theory.commutative-monoids.md) `M` to any family of
elements of `M` indexed by a
[finite type](univalent-combinatorics.finite-types.md).

## Sums over counted types

### Definition

```agda
sum-count-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2) →
  count A → (A → type-Commutative-Monoid M) → type-Commutative-Monoid M
sum-count-Commutative-Monoid M A (n , Fin-n≃A) f =
  sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv Fin-n≃A)
```

### Properties

#### Sums for a counted type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2)
  where

  htpy-sum-count-Commutative-Monoid :
    (c : count A) →
    {f g : A → type-Commutative-Monoid M} → (f ~ g) →
    sum-count-Commutative-Monoid M A c f ＝
    sum-count-Commutative-Monoid M A c g
  htpy-sum-count-Commutative-Monoid (nA , _) H =
    htpy-sum-fin-sequence-type-Commutative-Monoid M nA (λ i → H _)
```

#### Two counts for the same type produce equal sums

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2)
  where

  abstract
    eq-sum-count-equiv-Commutative-Monoid :
      (n : ℕ) → (equiv1 equiv2 : Fin n ≃ A) →
      (f : A → type-Commutative-Monoid M) →
      sum-count-Commutative-Monoid M A (n , equiv1) f ＝
      sum-count-Commutative-Monoid M A (n , equiv2) f
    eq-sum-count-equiv-Commutative-Monoid n equiv1 equiv2 f =
      equational-reasoning
      sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv equiv1)
      ＝
        sum-fin-sequence-type-Commutative-Monoid
          ( M)
          ( n)
          ( (f ∘ map-equiv equiv1) ∘ (map-inv-equiv equiv1 ∘ map-equiv equiv2))
        by
          preserves-sum-permutation-fin-sequence-type-Commutative-Monoid
            ( M)
            ( n)
            ( inv-equiv equiv1 ∘e equiv2)
            ( f ∘ map-equiv equiv1)
      ＝ sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv equiv2)
        by
          ap
            ( λ g →
              sum-fin-sequence-type-Commutative-Monoid
                ( M)
                ( n)
                ( f ∘ (g ∘ map-equiv equiv2)))
            ( eq-htpy (is-section-map-inv-equiv equiv1))

    eq-sum-count-Commutative-Monoid :
      (f : A → type-Commutative-Monoid M) (c1 c2 : count A) →
      sum-count-Commutative-Monoid M A c1 f ＝
      sum-count-Commutative-Monoid M A c2 f
    eq-sum-count-Commutative-Monoid f c1@(n , e1) c2@(_ , e2)
      with double-counting c1 c2
    ... | refl = eq-sum-count-equiv-Commutative-Monoid n e1 e2 f
```

#### Sums of counted families indexed by equivalent types are equal

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : UU l2) (B : UU l3) (H : A ≃ B)
  where

  abstract
    sum-equiv-count-Commutative-Monoid :
      (cA : count A) (cB : count B) (f : A → type-Commutative-Monoid M) →
      sum-count-Commutative-Monoid M A cA f ＝
      sum-count-Commutative-Monoid M B cB (f ∘ map-inv-equiv H)
    sum-equiv-count-Commutative-Monoid
      cA@(nA , Fin-nA≃A) cB@(_ , Fin-nB≃B) f
      with double-counting-equiv cA cB H
    ... | refl =
      preserves-sum-permutation-fin-sequence-type-Commutative-Monoid
        ( M)
        ( nA)
        ( inv-equiv Fin-nA≃A ∘e inv-equiv H ∘e Fin-nB≃B)
        ( _) ∙
      htpy-sum-fin-sequence-type-Commutative-Monoid
        ( M)
        ( nA)
        ( λ i → ap f (is-section-map-inv-equiv Fin-nA≃A _))
```

## Sums over finite types

### Definition

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  sum-finite-Commutative-Monoid :
    (f : type-Finite-Type A → type-Commutative-Monoid M) →
    type-Commutative-Monoid M
  sum-finite-Commutative-Monoid f =
    map-universal-property-set-quotient-trunc-Prop
      ( set-Commutative-Monoid M)
      ( λ c → sum-count-Commutative-Monoid M (type-Finite-Type A) c f)
      ( eq-sum-count-Commutative-Monoid M (type-Finite-Type A) f)
      ( is-finite-type-Finite-Type A)
```

### Properties

#### The sum over a finite type is its sum over any count for the type

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (cA : count (type-Finite-Type A))
  where

  abstract
    eq-sum-finite-sum-count-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      sum-finite-Commutative-Monoid M A f ＝
      sum-count-Commutative-Monoid M (type-Finite-Type A) cA f
    eq-sum-finite-sum-count-Commutative-Monoid f =
      equational-reasoning
        sum-finite-Commutative-Monoid M A f
        ＝
          sum-finite-Commutative-Monoid
            ( M)
            ( type-Finite-Type A , unit-trunc-Prop cA)
            ( f)
          by
            ap
              ( λ c →
                sum-finite-Commutative-Monoid
                  ( M)
                  ( type-Finite-Type A , c)
                  ( f))
              ( all-elements-equal-type-trunc-Prop
                ( is-finite-type-Finite-Type A)
                ( unit-trunc-Prop cA))
        ＝ sum-count-Commutative-Monoid M (type-Finite-Type A) cA f
          by
            htpy-universal-property-set-quotient-trunc-Prop
              ( set-Commutative-Monoid M)
              ( λ c →
                sum-count-Commutative-Monoid M (type-Finite-Type A) c f)
              ( eq-sum-count-Commutative-Monoid M (type-Finite-Type A) f)
              ( cA)
```

#### The sum over an empty finite type is zero

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  abstract
    eq-zero-sum-finite-is-empty-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      is-unit-Commutative-Monoid M (sum-finite-Commutative-Monoid M A f)
    eq-zero-sum-finite-is-empty-Commutative-Monoid =
      eq-sum-finite-sum-count-Commutative-Monoid M A (count-is-empty H)
```

#### A sum of zeroes is zero

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  sum-zero-finite-Commutative-Monoid :
    is-unit-Commutative-Monoid
      ( M)
      ( sum-finite-Commutative-Monoid
        ( M)
        ( A)
        ( λ _ → unit-Commutative-Monoid M))
  sum-zero-finite-Commutative-Monoid =
    let
      open
        do-syntax-trunc-Prop
          (is-unit-prop-Commutative-Monoid
            ( M)
            ( sum-finite-Commutative-Monoid
              ( M)
              ( A)
              ( λ _ → unit-Commutative-Monoid M)))
    in do
      cA ← is-finite-type-Finite-Type A
      eq-sum-finite-sum-count-Commutative-Monoid M A cA _ ∙
        sum-zero-fin-sequence-type-Commutative-Monoid M _
```

#### Sums over a finite type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : Finite-Type l2)
  where

  abstract
    htpy-sum-finite-Commutative-Monoid :
      {f g : type-Finite-Type A → type-Commutative-Monoid M} →
      f ~ g →
      sum-finite-Commutative-Monoid M A f ＝ sum-finite-Commutative-Monoid M A g
    htpy-sum-finite-Commutative-Monoid {f} {g} H =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( sum-finite-Commutative-Monoid M A f)
              ( sum-finite-Commutative-Monoid M A g))
      in do
        cA ← is-finite-type-Finite-Type A
        equational-reasoning
          sum-finite-Commutative-Monoid M A f
          ＝ sum-count-Commutative-Monoid M (type-Finite-Type A) cA f
            by eq-sum-finite-sum-count-Commutative-Monoid M A cA f
          ＝ sum-count-Commutative-Monoid M (type-Finite-Type A) cA g
            by htpy-sum-count-Commutative-Monoid M (type-Finite-Type A) cA H
          ＝ sum-finite-Commutative-Monoid M A g
            by inv (eq-sum-finite-sum-count-Commutative-Monoid M A cA g)
```

#### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  (H : equiv-Finite-Type A B)
  where

  abstract
    sum-equiv-finite-Commutative-Monoid :
      (f : type-Finite-Type A → type-Commutative-Monoid M) →
      sum-finite-Commutative-Monoid M A f ＝
      sum-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)
    sum-equiv-finite-Commutative-Monoid f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( sum-finite-Commutative-Monoid M A f)
              ( sum-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)))
      in do
        cA ← is-finite-type-Finite-Type A
        cB ← is-finite-type-Finite-Type B
        equational-reasoning
          sum-finite-Commutative-Monoid M A f
          ＝
            sum-count-Commutative-Monoid M (type-Finite-Type A) cA f
            by eq-sum-finite-sum-count-Commutative-Monoid M A cA f
          ＝
            sum-count-Commutative-Monoid
              ( M)
              ( type-Finite-Type B)
              ( cB)
              ( f ∘ map-inv-equiv H)
            by
              sum-equiv-count-Commutative-Monoid
                ( M)
                ( type-Finite-Type A)
                ( type-Finite-Type B)
                ( H)
                ( cA)
                ( cB)
                ( f)
          ＝ sum-finite-Commutative-Monoid M B (f ∘ map-inv-equiv H)
            by inv (eq-sum-finite-sum-count-Commutative-Monoid M B cB _)
```

#### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  where

  abstract
    distributive-distributive-sum-coproduct-finite-Commutative-Monoid :
      (f :
        type-Finite-Type A + type-Finite-Type B → type-Commutative-Monoid M) →
      sum-finite-Commutative-Monoid M (coproduct-Finite-Type A B) f ＝
      mul-Commutative-Monoid
        ( M)
        ( sum-finite-Commutative-Monoid M A (f ∘ inl))
        ( sum-finite-Commutative-Monoid M B (f ∘ inr))
    distributive-distributive-sum-coproduct-finite-Commutative-Monoid f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( sum-finite-Commutative-Monoid
                ( M)
                ( coproduct-Finite-Type A B)
                ( f))
              ( mul-Commutative-Monoid
                ( M)
                ( sum-finite-Commutative-Monoid M A (f ∘ inl))
                ( sum-finite-Commutative-Monoid M B (f ∘ inr))))
      in do
        cA@(nA , Fin-nA≃A) ← is-finite-type-Finite-Type A
        cB@(nB , Fin-nB≃B) ← is-finite-type-Finite-Type B
        equational-reasoning
          sum-finite-Commutative-Monoid M (coproduct-Finite-Type A B) f
          ＝
            sum-fin-sequence-type-Commutative-Monoid
              ( M)
              ( nA +ℕ nB)
              ( f ∘ map-equiv-count (count-coproduct cA cB))
            by
              eq-sum-finite-sum-count-Commutative-Monoid
                ( M)
                ( coproduct-Finite-Type A B)
                ( count-coproduct cA cB)
                ( f)
          ＝
            mul-Commutative-Monoid M
              ( sum-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nA)
                ( f ∘
                  map-equiv-count (count-coproduct cA cB) ∘
                  inl-coproduct-Fin nA nB))
              ( sum-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nB)
                ( f ∘
                  map-equiv-count (count-coproduct cA cB) ∘
                  inr-coproduct-Fin nA nB))
            by
              split-sum-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nA)
                ( nB)
                ( f ∘ map-equiv-count (count-coproduct cA cB))
          ＝
            mul-Commutative-Monoid
              ( M)
              ( sum-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nA)
                ( f ∘ inl ∘ map-equiv-count cA))
              ( sum-fin-sequence-type-Commutative-Monoid
                ( M)
                ( nB)
                ( f ∘ inr ∘ map-equiv-count cB))
            by
              ap-mul-Commutative-Monoid
                ( M)
                ( ap
                  ( λ g → sum-fin-sequence-type-Commutative-Monoid M nA (f ∘ g))
                  ( eq-htpy
                    ( map-equiv-count-coproduct-inl-coproduct-Fin cA cB)))
                ( ap
                  ( λ g → sum-fin-sequence-type-Commutative-Monoid M nB (f ∘ g))
                  ( eq-htpy
                    ( map-equiv-count-coproduct-inr-coproduct-Fin cA cB)))
          ＝
            mul-Commutative-Monoid
              ( M)
              ( sum-finite-Commutative-Monoid M A (f ∘ inl))
              ( sum-finite-Commutative-Monoid M B (f ∘ inr))
            by
              inv
                ( ap-mul-Commutative-Monoid
                  ( M)
                  ( eq-sum-finite-sum-count-Commutative-Monoid
                    ( M)
                    ( A)
                    ( cA)
                    ( f ∘ inl))
                  ( eq-sum-finite-sum-count-Commutative-Monoid
                    ( M)
                    ( B)
                    ( cB)
                    ( f ∘ inr)))
```

#### Sums distribute over dependent pair types

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    sum-fin-finite-Σ-Commutative-Monoid :
      (n : ℕ) →
      {l2 : Level} →
      (B : Fin n → Finite-Type l2) →
      (f : (k : Fin n) → type-Finite-Type (B k) → type-Commutative-Monoid M) →
      sum-fin-sequence-type-Commutative-Monoid M n
        (λ k → sum-finite-Commutative-Monoid M (B k) (f k)) ＝
      sum-finite-Commutative-Monoid
        M (Σ-Finite-Type (Fin-Finite-Type n) B) (ind-Σ f)
    sum-fin-finite-Σ-Commutative-Monoid zero-ℕ B f =
      inv
        ( eq-zero-sum-finite-is-empty-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type zero-ℕ) B)
          ( λ ())
          ( ind-Σ f))
    sum-fin-finite-Σ-Commutative-Monoid (succ-ℕ n) B f =
      equational-reasoning
      sum-fin-sequence-type-Commutative-Monoid
        ( M)
        ( succ-ℕ n)
        ( λ k → sum-finite-Commutative-Monoid M (B k) (f k))
      ＝
        mul-Commutative-Monoid
          ( M)
          ( sum-fin-sequence-type-Commutative-Monoid
            ( M)
            ( n)
            ( λ k →
              sum-finite-Commutative-Monoid
                ( M)
                ( B (inl k))
                ( f (inl k))))
          ( sum-finite-Commutative-Monoid
            ( M)
            ( B (inr star))
            ( f (inr star)))
        by
          cons-sum-fin-sequence-type-Commutative-Monoid
            ( M)
            ( n)
            ( λ k → sum-finite-Commutative-Monoid M (B k) (f k))
            ( refl)
      ＝
        mul-Commutative-Monoid
          ( M)
          ( sum-finite-Commutative-Monoid
            ( M)
            ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
            ( ind-Σ (f ∘ inl)))
          ( sum-finite-Commutative-Monoid
            ( M)
            ( B (inr star))
            ( f (inr star)))
        by
          ap-mul-Commutative-Monoid
            ( M)
            ( sum-fin-finite-Σ-Commutative-Monoid
              ( n)
              ( B ∘ inl)
              ( f ∘ inl))
            ( refl)
      ＝
        sum-finite-Commutative-Monoid
          ( M)
          ( coproduct-Finite-Type
            ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
            ( B (inr star)))
          ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star)))
        by
          inv
            ( distributive-distributive-sum-coproduct-finite-Commutative-Monoid
              ( M)
              ( Σ-Finite-Type (Fin-Finite-Type n) (B ∘ inl))
              ( B (inr star))
              ( rec-coproduct (ind-Σ (f ∘ inl)) (f (inr star))))
      ＝
        sum-finite-Commutative-Monoid
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
          sum-equiv-finite-Commutative-Monoid
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
        sum-finite-Commutative-Monoid
          ( M)
          ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
          ( ind-Σ f)
        by
          htpy-sum-finite-Commutative-Monoid
            ( M)
            ( Σ-Finite-Type (Fin-Finite-Type (succ-ℕ n)) B)
            ( λ { (inl k , b) → refl ; (inr k , b) → refl})

module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  abstract
    sum-Σ-finite-Commutative-Monoid :
      (f :
        (a : type-Finite-Type A) →
        type-Finite-Type (B a) →
        type-Commutative-Monoid M) →
      sum-finite-Commutative-Monoid M (Σ-Finite-Type A B) (ind-Σ f) ＝
      sum-finite-Commutative-Monoid
        ( M)
        ( A)
        ( λ a → sum-finite-Commutative-Monoid M (B a) (f a))
    sum-Σ-finite-Commutative-Monoid f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Monoid M)
              ( sum-finite-Commutative-Monoid M (Σ-Finite-Type A B) (ind-Σ f))
              ( sum-finite-Commutative-Monoid
                ( M)
                ( A)
                ( λ a → sum-finite-Commutative-Monoid M (B a) (f a))))
      in do
        cA@(nA , Fin-nA≃A) ← is-finite-type-Finite-Type A
        equational-reasoning
          sum-finite-Commutative-Monoid M (Σ-Finite-Type A B) (ind-Σ f)
          ＝
            sum-finite-Commutative-Monoid
              ( M)
              ( Σ-Finite-Type (Fin-Finite-Type nA) (B ∘ map-equiv Fin-nA≃A))
              ( ind-Σ (f ∘ map-equiv Fin-nA≃A))
            by
              sum-equiv-finite-Commutative-Monoid
                ( M)
                ( Σ-Finite-Type A B)
                ( Σ-Finite-Type (Fin-Finite-Type nA) (B ∘ map-equiv Fin-nA≃A))
                ( inv-equiv
                  ( equiv-Σ-equiv-base (type-Finite-Type ∘ B) Fin-nA≃A))
                ( _)
          ＝
            sum-count-Commutative-Monoid
              ( M)
              ( type-Finite-Type A)
              ( cA)
              ( λ a → sum-finite-Commutative-Monoid M (B a) (f a))
            by
              inv
                ( sum-fin-finite-Σ-Commutative-Monoid
                  ( M)
                  ( nA)
                  ( B ∘ map-equiv Fin-nA≃A)
                  ( f ∘ map-equiv Fin-nA≃A))
          ＝
            sum-finite-Commutative-Monoid
              ( M)
              ( A)
              ( λ a → sum-finite-Commutative-Monoid M (B a) (f a))
            by inv (eq-sum-finite-sum-count-Commutative-Monoid M A cA _)
```

#### Sums over the unit type

```agda
module _
  {l : Level} (M : Commutative-Monoid l)
  where

  abstract
    sum-finite-unit-type-Commutative-Monoid :
      (f : unit → type-Commutative-Monoid M) →
      sum-finite-Commutative-Monoid M unit-Finite-Type f ＝ f star
    sum-finite-unit-type-Commutative-Monoid f =
      equational-reasoning
        sum-finite-Commutative-Monoid M unit-Finite-Type f
        ＝
          sum-count-Commutative-Monoid
            ( M)
            ( unit)
            ( count-unit)
            ( f)
          by
            eq-sum-finite-sum-count-Commutative-Monoid
              ( M)
              ( unit-Finite-Type)
              ( count-unit)
              ( f)
        ＝ f star by compute-sum-one-element-Commutative-Monoid M _
```
