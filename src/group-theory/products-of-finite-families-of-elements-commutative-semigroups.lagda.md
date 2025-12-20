# Products of finite families of elements in commutative semigroups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.products-of-finite-families-of-elements-commutative-semigroups where
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
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-empty-type
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels

open import group-theory.commutative-semigroups
open import group-theory.products-of-finite-sequences-of-elements-commutative-semigroups

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.coproducts-inhabited-finite-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "product operation" Disambiguation="of a finite family of elements of a commutative semigroup" Agda=product-finite-Commutative-Semigroup}}
extends the binary operation on a
[commutative semigroup](group-theory.commutative-semigroups.md) `G` to any
family of elements of `G` indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md).

## Products over counted types

### Definition

```agda
product-count-Commutative-Semigroup :
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : UU l2) →
  is-inhabited A → count A → (A → type-Commutative-Semigroup G) →
  type-Commutative-Semigroup G
product-count-Commutative-Semigroup G A |A| cA@(zero-ℕ , _) _ =
  ex-falso
    ( is-nonempty-is-inhabited
      ( |A|)
      ( is-empty-is-zero-number-of-elements-count cA refl))
product-count-Commutative-Semigroup G A _ (succ-ℕ n , Fin-sn≃A) f =
  product-fin-sequence-type-Commutative-Semigroup G n (f ∘ map-equiv Fin-sn≃A)
```

### Properties

#### Products for a counted type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : UU l2)
  (|A| : is-inhabited A)
  where

  abstract
    htpy-product-count-Commutative-Semigroup :
      (c : count A) →
      {f g : A → type-Commutative-Semigroup G} → (f ~ g) →
      product-count-Commutative-Semigroup G A |A| c f ＝
      product-count-Commutative-Semigroup G A |A| c g
    htpy-product-count-Commutative-Semigroup cA@(zero-ℕ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count cA refl))
    htpy-product-count-Commutative-Semigroup (succ-ℕ nA , _) H =
      htpy-product-fin-sequence-type-Commutative-Semigroup G nA (λ i → H _)
```

#### Two counts for the same type produce equal products

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1)
  (A : UU l2) (|A| : is-inhabited A)
  where

  abstract
    eq-product-count-equiv-Commutative-Semigroup :
      (n : ℕ) → (equiv1 equiv2 : Fin (succ-ℕ n) ≃ A) →
      (f : A → type-Commutative-Semigroup G) →
      product-count-Commutative-Semigroup G A |A| (succ-ℕ n , equiv1) f ＝
      product-count-Commutative-Semigroup G A |A| (succ-ℕ n , equiv2) f
    eq-product-count-equiv-Commutative-Semigroup n equiv1 equiv2 f =
      equational-reasoning
      product-fin-sequence-type-Commutative-Semigroup G n (f ∘ map-equiv equiv1)
      ＝
        product-fin-sequence-type-Commutative-Semigroup
          ( G)
          ( n)
          ( f ∘ map-equiv equiv1 ∘ map-inv-equiv equiv1 ∘ map-equiv equiv2)
        by
          preserves-product-permutation-fin-sequence-type-Commutative-Semigroup
            ( G)
            ( n)
            ( inv-equiv equiv1 ∘e equiv2)
            ( f ∘ map-equiv equiv1)
      ＝
        product-fin-sequence-type-Commutative-Semigroup
          ( G)
          ( n)
          ( f ∘ map-equiv equiv2)
        by
          ap
            ( λ g →
              product-fin-sequence-type-Commutative-Semigroup
                ( G)
                ( n)
                ( f ∘ g ∘ map-equiv equiv2))
            ( eq-htpy (is-section-map-inv-equiv equiv1))

    eq-product-count-Commutative-Semigroup :
      (f : A → type-Commutative-Semigroup G) (c1 c2 : count A) →
      product-count-Commutative-Semigroup G A |A| c1 f ＝
      product-count-Commutative-Semigroup G A |A| c2 f
    eq-product-count-Commutative-Semigroup f c1@(zero-ℕ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count c1 refl))
    eq-product-count-Commutative-Semigroup f c1@(succ-ℕ n , e1) c2@(_ , e2)
      with double-counting c1 c2
    ... | refl = eq-product-count-equiv-Commutative-Semigroup n e1 e2 f
```

#### Products of counted families indexed by equivalent types are equal

```agda
module _
  {l1 l2 l3 : Level} (G : Commutative-Semigroup l1)
  (A : UU l2) (|A| : is-inhabited A) (B : UU l3) (|B| : is-inhabited B)
  (H : A ≃ B)
  where

  abstract
    product-equiv-count-Commutative-Semigroup :
      (cA : count A) (cB : count B) (f : A → type-Commutative-Semigroup G) →
      product-count-Commutative-Semigroup G A |A| cA f ＝
      product-count-Commutative-Semigroup G B |B| cB (f ∘ map-inv-equiv H)
    product-equiv-count-Commutative-Semigroup
      cA@(zero-ℕ , _) _ _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count cA refl))
    product-equiv-count-Commutative-Semigroup
      cA@(succ-ℕ nA , Fin-nA≃A) cB@(_ , Fin-nB≃B) f
      with double-counting-equiv cA cB H
    ... | refl =
      ( preserves-product-permutation-fin-sequence-type-Commutative-Semigroup
        ( G)
        ( nA)
        ( inv-equiv Fin-nA≃A ∘e inv-equiv H ∘e Fin-nB≃B)
        ( _)) ∙
      ( htpy-product-fin-sequence-type-Commutative-Semigroup
        ( G)
        ( nA)
        ( λ i → ap f (is-section-map-inv-equiv Fin-nA≃A _)))
```

#### Products of coproducts of counted types

```agda
module _
  {l1 l2 l3 : Level} (G : Commutative-Semigroup l1)
  (A : UU l2) (|A| : is-inhabited A) (B : UU l3) (|B| : is-inhabited B)
  (|A+B| : is-inhabited (A + B))
  where

  abstract
    distributive-product-coproduct-count-Commutative-Semigroup :
      (cA : count A) (cB : count B) →
      (f : (A + B) → type-Commutative-Semigroup G) →
      product-count-Commutative-Semigroup
        ( G)
        ( A + B)
        ( |A+B|)
        ( count-coproduct cA cB)
        ( f) ＝
      mul-Commutative-Semigroup G
        ( product-count-Commutative-Semigroup G A |A| cA (f ∘ inl))
        ( product-count-Commutative-Semigroup G B |B| cB (f ∘ inr))
    distributive-product-coproduct-count-Commutative-Semigroup
      cA@(succ-ℕ nA , Fin-snA≃A) cB@(succ-ℕ nB , Fin-snB≃B) f =
      ( split-product-fin-sequence-type-Commutative-Semigroup G nA nB _) ∙
      ( ap-mul-Commutative-Semigroup G
        ( htpy-product-fin-sequence-type-Commutative-Semigroup G nA
          ( ap f ∘ map-equiv-count-coproduct-inl-coproduct-Fin cA cB))
        ( htpy-product-fin-sequence-type-Commutative-Semigroup G nB
          ( ap f ∘ map-equiv-count-coproduct-inr-coproduct-Fin cA cB)))
    distributive-product-coproduct-count-Commutative-Semigroup
      cA@(zero-ℕ , _) cB@(succ-ℕ _ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count cA refl))
    distributive-product-coproduct-count-Commutative-Semigroup
      cA@(zero-ℕ , _) cB@(zero-ℕ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count cA refl))
    distributive-product-coproduct-count-Commutative-Semigroup
      cA@(succ-ℕ _ , _) cB@(zero-ℕ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |B|)
          ( is-empty-is-zero-number-of-elements-count cB refl))
```

## Products over finite types

### Definition

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : Inhabited-Finite-Type l2)
  where

  opaque
    product-finite-Commutative-Semigroup :
      (f : type-Inhabited-Finite-Type A → type-Commutative-Semigroup G) →
      type-Commutative-Semigroup G
    product-finite-Commutative-Semigroup f =
      map-universal-property-set-quotient-trunc-Prop
        ( set-Commutative-Semigroup G)
        ( λ c →
          product-count-Commutative-Semigroup G
            ( type-Inhabited-Finite-Type A)
            ( is-inhabited-type-Inhabited-Finite-Type A)
            ( c)
            ( f))
        ( eq-product-count-Commutative-Semigroup G
          ( type-Inhabited-Finite-Type A)
          ( is-inhabited-type-Inhabited-Finite-Type A)
          ( f))
        ( is-finite-Inhabited-Finite-Type A)
```

### Properties

#### The product over a finite type is its product over any count for the type

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1)
  (A : Inhabited-Finite-Type l2) (cA : count (type-Inhabited-Finite-Type A))
  where

  abstract opaque
    unfolding product-finite-Commutative-Semigroup

    eq-product-finite-product-count-Commutative-Semigroup :
      (f : type-Inhabited-Finite-Type A → type-Commutative-Semigroup G) →
      product-finite-Commutative-Semigroup G A f ＝
      product-count-Commutative-Semigroup G
        ( type-Inhabited-Finite-Type A)
        ( is-inhabited-type-Inhabited-Finite-Type A) cA f
    eq-product-finite-product-count-Commutative-Semigroup f =
      ( ap
        ( λ c → product-finite-Commutative-Semigroup G ((_ , c) , _) f)
        ( all-elements-equal-type-trunc-Prop _ _)) ∙
      ( htpy-universal-property-set-quotient-trunc-Prop
        ( set-Commutative-Semigroup G)
        ( λ c →
          product-count-Commutative-Semigroup G
            ( type-Inhabited-Finite-Type A)
            ( is-inhabited-type-Inhabited-Finite-Type A)
            ( c)
            ( f))
        ( eq-product-count-Commutative-Semigroup G
          ( type-Inhabited-Finite-Type A)
          ( is-inhabited-type-Inhabited-Finite-Type A)
          ( f))
        ( cA))
```

#### Products over a finite type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : Inhabited-Finite-Type l2)
  where

  abstract
    htpy-product-finite-Commutative-Semigroup :
      {f g : type-Inhabited-Finite-Type A → type-Commutative-Semigroup G} →
      f ~ g →
      product-finite-Commutative-Semigroup G A f ＝
      product-finite-Commutative-Semigroup G A g
    htpy-product-finite-Commutative-Semigroup {f} {g} H =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Semigroup G)
              ( product-finite-Commutative-Semigroup G A f)
              ( product-finite-Commutative-Semigroup G A g))
      in do
        cA ← is-finite-Inhabited-Finite-Type A
        equational-reasoning
          product-finite-Commutative-Semigroup G A f
          ＝
            product-count-Commutative-Semigroup G
              ( type-Inhabited-Finite-Type A)
              ( is-inhabited-type-Inhabited-Finite-Type A)
              ( cA)
              ( f)
            by eq-product-finite-product-count-Commutative-Semigroup G A cA f
          ＝
            product-count-Commutative-Semigroup G
              ( type-Inhabited-Finite-Type A)
              ( is-inhabited-type-Inhabited-Finite-Type A)
              ( cA)
              ( g)
            by
              htpy-product-count-Commutative-Semigroup
                ( G)
                ( type-Inhabited-Finite-Type A)
                ( is-inhabited-type-Inhabited-Finite-Type A)
                ( cA)
                ( H)
          ＝ product-finite-Commutative-Semigroup G A g
            by
              inv
                ( eq-product-finite-product-count-Commutative-Semigroup
                  ( G)
                  ( A)
                  ( cA)
                  ( g))
```

#### Products over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (G : Commutative-Semigroup l1)
  (A : Inhabited-Finite-Type l2)
  (B : Inhabited-Finite-Type l3)
  (H : equiv-Inhabited-Finite-Type A B)
  where

  abstract
    product-equiv-finite-Commutative-Semigroup :
      (f : type-Inhabited-Finite-Type A → type-Commutative-Semigroup G) →
      product-finite-Commutative-Semigroup G A f ＝
      product-finite-Commutative-Semigroup G B (f ∘ map-inv-equiv H)
    product-equiv-finite-Commutative-Semigroup f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Semigroup G)
              ( product-finite-Commutative-Semigroup G A f)
              ( product-finite-Commutative-Semigroup G B (f ∘ map-inv-equiv H)))
      in do
        cA ← is-finite-Inhabited-Finite-Type A
        cB ← is-finite-Inhabited-Finite-Type B
        ( ( eq-product-finite-product-count-Commutative-Semigroup G _ cA f) ∙
          ( product-equiv-count-Commutative-Semigroup G _ _ _ _ H cA cB f) ∙
          ( inv
            ( eq-product-finite-product-count-Commutative-Semigroup G _ cB _)))
```

### Products over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (G : Commutative-Semigroup l1)
  (A : Inhabited-Finite-Type l2)
  (B : Inhabited-Finite-Type l3)
  where

  abstract
    distributive-product-coproduct-finite-Commutative-Semigroup :
      (f :
        type-Inhabited-Finite-Type A + type-Inhabited-Finite-Type B →
        type-Commutative-Semigroup G) →
      product-finite-Commutative-Semigroup
        ( G)
        ( coproduct-Inhabited-Finite-Type A B)
        ( f) ＝
      mul-Commutative-Semigroup
        ( G)
        ( product-finite-Commutative-Semigroup G A (f ∘ inl))
        ( product-finite-Commutative-Semigroup G B (f ∘ inr))
    distributive-product-coproduct-finite-Commutative-Semigroup f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Semigroup G)
              ( product-finite-Commutative-Semigroup
                ( G)
                ( coproduct-Inhabited-Finite-Type A B)
                ( f))
              ( mul-Commutative-Semigroup
                ( G)
                ( product-finite-Commutative-Semigroup G A (f ∘ inl))
                ( product-finite-Commutative-Semigroup G B (f ∘ inr))))
      in do
        cA ← is-finite-Inhabited-Finite-Type A
        cB ← is-finite-Inhabited-Finite-Type B
        ( ( eq-product-finite-product-count-Commutative-Semigroup
            ( G)
            ( coproduct-Inhabited-Finite-Type A B)
            ( count-coproduct cA cB)
            ( f)) ∙
          ( distributive-product-coproduct-count-Commutative-Semigroup
            ( G)
            ( type-Inhabited-Finite-Type A)
            ( is-inhabited-type-Inhabited-Finite-Type A)
            ( type-Inhabited-Finite-Type B)
            ( is-inhabited-type-Inhabited-Finite-Type B)
            ( is-inhabited-type-Inhabited-Finite-Type
              ( coproduct-Inhabited-Finite-Type A B))
            ( cA)
            ( cB)
            ( f)) ∙
          ( ap-mul-Commutative-Semigroup
            ( G)
            ( inv
              ( eq-product-finite-product-count-Commutative-Semigroup
                ( G)
                ( A)
                ( cA)
                ( f ∘ inl)))
            ( inv
              ( eq-product-finite-product-count-Commutative-Semigroup
                ( G)
                ( B)
                ( cB)
                ( f ∘ inr)))))
```
