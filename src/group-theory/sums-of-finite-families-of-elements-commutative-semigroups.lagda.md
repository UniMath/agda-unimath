# Sums of finite families of elements in commutative semigroups

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.sums-of-finite-families-of-elements-commutative-semigroups where
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
open import group-theory.sums-of-finite-sequences-of-elements-commutative-semigroups

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
{{#concept "sum operation" Disambiguation="of a finite family of elements of a commutative semigroup" WD="sum" WDID=Q218005 Agda=sum-finite-Commutative-Semigroup}}
extends the binary operation on a
[commutative semigroup](group-theory.commutative-semigroups.md) `G` to any
family of elements of `G` indexed by an
[inhabited](foundation.inhabited-types.md)
[finite type](univalent-combinatorics.finite-types.md).

We use additive terminology consistently with the linear algebra definition of
[finite sequences in commutative semigroups](linear-algebra.finite-sequences-in-commutative-semigroups.md)
despite the use of multiplicative terminology for commutative semigroups in
general.

## Sums over counted types

### Definition

```agda
sum-count-Commutative-Semigroup :
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : UU l2) →
  is-inhabited A → count A → (A → type-Commutative-Semigroup G) →
  type-Commutative-Semigroup G
sum-count-Commutative-Semigroup G A |A| cA@(zero-ℕ , _) _ =
  ex-falso
    ( is-nonempty-is-inhabited
      ( |A|)
      ( is-empty-is-zero-number-of-elements-count cA refl))
sum-count-Commutative-Semigroup G A _ (succ-ℕ n , Fin-sn≃A) f =
  sum-fin-sequence-type-Commutative-Semigroup G n (f ∘ map-equiv Fin-sn≃A)
```

### Properties

#### Sums for a counted type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : UU l2)
  (|A| : is-inhabited A)
  where

  htpy-sum-count-Commutative-Semigroup :
    (c : count A) →
    {f g : A → type-Commutative-Semigroup G} → (f ~ g) →
    sum-count-Commutative-Semigroup G A |A| c f ＝
    sum-count-Commutative-Semigroup G A |A| c g
  htpy-sum-count-Commutative-Semigroup cA@(zero-ℕ , _) _ =
    ex-falso
      ( is-nonempty-is-inhabited
        ( |A|)
        ( is-empty-is-zero-number-of-elements-count cA refl))
  htpy-sum-count-Commutative-Semigroup (succ-ℕ nA , _) H =
    htpy-sum-fin-sequence-type-Commutative-Semigroup G nA (λ i → H _)
```

#### Two counts for the same type produce equal sums

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : UU l2)
  (|A| : is-inhabited A)
  where

  abstract
    eq-sum-count-equiv-Commutative-Semigroup :
      (n : ℕ) → (equiv1 equiv2 : Fin (succ-ℕ n) ≃ A) →
      (f : A → type-Commutative-Semigroup G) →
      sum-count-Commutative-Semigroup G A |A| (succ-ℕ n , equiv1) f ＝
      sum-count-Commutative-Semigroup G A |A| (succ-ℕ n , equiv2) f
    eq-sum-count-equiv-Commutative-Semigroup n equiv1 equiv2 f =
      equational-reasoning
      sum-fin-sequence-type-Commutative-Semigroup G n (f ∘ map-equiv equiv1)
      ＝
        sum-fin-sequence-type-Commutative-Semigroup
          ( G)
          ( n)
          ( (f ∘ map-equiv equiv1) ∘ (map-inv-equiv equiv1 ∘ map-equiv equiv2))
        by
          preserves-sum-permutation-fin-sequence-type-Commutative-Semigroup
            ( G)
            ( n)
            ( inv-equiv equiv1 ∘e equiv2)
            ( f ∘ map-equiv equiv1)
      ＝ sum-fin-sequence-type-Commutative-Semigroup G n (f ∘ map-equiv equiv2)
        by
          ap
            ( λ g →
              sum-fin-sequence-type-Commutative-Semigroup
                ( G)
                ( n)
                ( f ∘ (g ∘ map-equiv equiv2)))
            ( eq-htpy (is-section-map-inv-equiv equiv1))

    eq-sum-count-Commutative-Semigroup :
      (f : A → type-Commutative-Semigroup G) (c1 c2 : count A) →
      sum-count-Commutative-Semigroup G A |A| c1 f ＝
      sum-count-Commutative-Semigroup G A |A| c2 f
    eq-sum-count-Commutative-Semigroup f c1@(zero-ℕ , _) _ =
      ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count c1 refl))
    eq-sum-count-Commutative-Semigroup f c1@(succ-ℕ n , e1) c2@(_ , e2)
      with double-counting c1 c2
    ... | refl = eq-sum-count-equiv-Commutative-Semigroup n e1 e2 f
```

#### Sums of counted families indexed by equivalent types are equal

```agda
module _
  {l1 l2 l3 : Level} (G : Commutative-Semigroup l1)
  (A : UU l2) (|A| : is-inhabited A) (B : UU l3) (|B| : is-inhabited B)
  (H : A ≃ B)
  where

  abstract
    sum-equiv-count-Commutative-Semigroup :
      (cA : count A) (cB : count B) (f : A → type-Commutative-Semigroup G) →
      sum-count-Commutative-Semigroup G A |A| cA f ＝
      sum-count-Commutative-Semigroup G B |B| cB (f ∘ map-inv-equiv H)
    sum-equiv-count-Commutative-Semigroup
      cA@(zero-ℕ , _) _ _ =
        ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count cA refl))
    sum-equiv-count-Commutative-Semigroup
      cA@(succ-ℕ nA , Fin-nA≃A) cB@(_ , Fin-nB≃B) f
      with double-counting-equiv cA cB H
    ... | refl =
      preserves-sum-permutation-fin-sequence-type-Commutative-Semigroup
        ( G)
        ( nA)
        ( inv-equiv Fin-nA≃A ∘e inv-equiv H ∘e Fin-nB≃B)
        ( _) ∙
      htpy-sum-fin-sequence-type-Commutative-Semigroup
        ( G)
        ( nA)
        ( λ i → ap f (is-section-map-inv-equiv Fin-nA≃A _))
```

#### Sums of coproducts of counted types

```agda
module _
  {l1 l2 l3 : Level} (G : Commutative-Semigroup l1)
  (A : UU l2) (|A| : is-inhabited A) (B : UU l3) (|B| : is-inhabited B)
  (|A+B| : is-inhabited (A + B))
  where

  abstract
    distributive-sum-coproduct-count-Commutative-Semigroup :
      (cA : count A) (cB : count B) →
      (f : (A + B) → type-Commutative-Semigroup G) →
      sum-count-Commutative-Semigroup
        ( G)
        ( A + B)
        ( |A+B|)
        ( count-coproduct cA cB)
        ( f) ＝
      mul-Commutative-Semigroup G
        ( sum-count-Commutative-Semigroup G A |A| cA (f ∘ inl))
        ( sum-count-Commutative-Semigroup G B |B| cB (f ∘ inr))
    distributive-sum-coproduct-count-Commutative-Semigroup
      cA@(succ-ℕ nA , Fin-snA≃A) cB@(succ-ℕ nB , Fin-snB≃B) f =
        split-sum-fin-sequence-type-Commutative-Semigroup G nA nB _ ∙
        ap-mul-Commutative-Semigroup G
          ( htpy-sum-fin-sequence-type-Commutative-Semigroup G nA
            ( λ i → ap f (map-equiv-count-coproduct-inl-coproduct-Fin cA cB i)))
          ( htpy-sum-fin-sequence-type-Commutative-Semigroup G nB
            ( λ i → ap f (map-equiv-count-coproduct-inr-coproduct-Fin cA cB i)))
    distributive-sum-coproduct-count-Commutative-Semigroup
      cA@(zero-ℕ , _) cB@(succ-ℕ _ , _) _ =
        ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count cA refl))
    distributive-sum-coproduct-count-Commutative-Semigroup
      cA@(zero-ℕ , _) cB@(zero-ℕ , _) _ =
        ex-falso
        ( is-nonempty-is-inhabited
          ( |A|)
          ( is-empty-is-zero-number-of-elements-count cA refl))
    distributive-sum-coproduct-count-Commutative-Semigroup
      cA@(succ-ℕ _ , _) cB@(zero-ℕ , _) _ =
        ex-falso
        ( is-nonempty-is-inhabited
          ( |B|)
          ( is-empty-is-zero-number-of-elements-count cB refl))
```

## Sums over finite types

### Definition

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : Finite-Type l2)
  (|A| : is-inhabited-Finite-Type A)
  where

  sum-finite-Commutative-Semigroup :
    (f : type-Finite-Type A → type-Commutative-Semigroup G) →
    type-Commutative-Semigroup G
  sum-finite-Commutative-Semigroup f =
    map-universal-property-set-quotient-trunc-Prop
      ( set-Commutative-Semigroup G)
      ( λ c → sum-count-Commutative-Semigroup G (type-Finite-Type A) |A| c f)
      ( eq-sum-count-Commutative-Semigroup G (type-Finite-Type A) |A| f)
      ( is-finite-type-Finite-Type A)
```

### Properties

#### The sum over a finite type is its sum over any count for the type

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1)
  (A : Finite-Type l2) (|A| : is-inhabited-Finite-Type A)
  (cA : count (type-Finite-Type A))
  where

  abstract
    eq-sum-finite-sum-count-Commutative-Semigroup :
      (f : type-Finite-Type A → type-Commutative-Semigroup G) →
      sum-finite-Commutative-Semigroup G A |A| f ＝
      sum-count-Commutative-Semigroup G (type-Finite-Type A) |A| cA f
    eq-sum-finite-sum-count-Commutative-Semigroup f =
      ap
        ( λ c →
          sum-finite-Commutative-Semigroup
            ( G)
            ( type-Finite-Type A , c)
            ( |A|)
            ( f))
        ( all-elements-equal-type-trunc-Prop
          ( is-finite-type-Finite-Type A)
          ( unit-trunc-Prop cA)) ∙
      htpy-universal-property-set-quotient-trunc-Prop
        ( set-Commutative-Semigroup G)
        ( λ c → sum-count-Commutative-Semigroup G (type-Finite-Type A) |A| c f)
        ( eq-sum-count-Commutative-Semigroup G (type-Finite-Type A) |A| f)
        ( cA)
```

#### Sums over a finite type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (G : Commutative-Semigroup l1) (A : Finite-Type l2)
  (|A| : is-inhabited-Finite-Type A)
  where

  abstract
    htpy-sum-finite-Commutative-Semigroup :
      {f g : type-Finite-Type A → type-Commutative-Semigroup G} →
      f ~ g →
      sum-finite-Commutative-Semigroup G A |A| f ＝
      sum-finite-Commutative-Semigroup G A |A| g
    htpy-sum-finite-Commutative-Semigroup {f} {g} H =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Semigroup G)
              ( sum-finite-Commutative-Semigroup G A |A| f)
              ( sum-finite-Commutative-Semigroup G A |A| g))
      in do
        cA ← is-finite-type-Finite-Type A
        equational-reasoning
          sum-finite-Commutative-Semigroup G A |A| f
          ＝ sum-count-Commutative-Semigroup G (type-Finite-Type A) |A| cA f
            by eq-sum-finite-sum-count-Commutative-Semigroup G A |A| cA f
          ＝ sum-count-Commutative-Semigroup G (type-Finite-Type A) |A| cA g
            by
              htpy-sum-count-Commutative-Semigroup
                ( G)
                ( type-Finite-Type A)
                ( |A|)
                ( cA)
                ( H)
          ＝ sum-finite-Commutative-Semigroup G A |A| g
            by inv (eq-sum-finite-sum-count-Commutative-Semigroup G A |A| cA g)
```

#### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (G : Commutative-Semigroup l1)
  (A : Finite-Type l2) (|A| : is-inhabited-Finite-Type A)
  (B : Finite-Type l3) (|B| : is-inhabited-Finite-Type B)
  (H : equiv-Finite-Type A B)
  where

  abstract
    sum-equiv-finite-Commutative-Semigroup :
      (f : type-Finite-Type A → type-Commutative-Semigroup G) →
      sum-finite-Commutative-Semigroup G A |A| f ＝
      sum-finite-Commutative-Semigroup G B |B| (f ∘ map-inv-equiv H)
    sum-equiv-finite-Commutative-Semigroup f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Semigroup G)
              ( sum-finite-Commutative-Semigroup G A |A| f)
              ( sum-finite-Commutative-Semigroup G B |B| (f ∘ map-inv-equiv H)))
      in do
        cA ← is-finite-type-Finite-Type A
        cB ← is-finite-type-Finite-Type B
        equational-reasoning
          sum-finite-Commutative-Semigroup G A |A| f
          ＝
            sum-count-Commutative-Semigroup G (type-Finite-Type A) |A| cA f
            by eq-sum-finite-sum-count-Commutative-Semigroup G A |A| cA f
          ＝
            sum-count-Commutative-Semigroup
              ( G)
              ( type-Finite-Type B)
              ( |B|)
              ( cB)
              ( f ∘ map-inv-equiv H)
            by
              sum-equiv-count-Commutative-Semigroup
                ( G)
                ( type-Finite-Type A)
                ( |A|)
                ( type-Finite-Type B)
                ( |B|)
                ( H)
                ( cA)
                ( cB)
                ( f)
          ＝ sum-finite-Commutative-Semigroup G B |B| (f ∘ map-inv-equiv H)
            by inv (eq-sum-finite-sum-count-Commutative-Semigroup G B |B| cB _)
```

### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (G : Commutative-Semigroup l1)
  (A : Finite-Type l2) (|A| : is-inhabited-Finite-Type A)
  (B : Finite-Type l3) (|B| : is-inhabited-Finite-Type B)
  (|A+B| : is-inhabited-Finite-Type (coproduct-Finite-Type A B))
  where

  abstract
    distributive-distributive-sum-coproduct-finite-Commutative-Semigroup :
      (f :
        type-Finite-Type A + type-Finite-Type B →
        type-Commutative-Semigroup G) →
      sum-finite-Commutative-Semigroup G (coproduct-Finite-Type A B) |A+B| f ＝
      mul-Commutative-Semigroup
        ( G)
        ( sum-finite-Commutative-Semigroup G A |A| (f ∘ inl))
        ( sum-finite-Commutative-Semigroup G B |B| (f ∘ inr))
    distributive-distributive-sum-coproduct-finite-Commutative-Semigroup f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Commutative-Semigroup G)
              ( sum-finite-Commutative-Semigroup
                ( G)
                ( coproduct-Finite-Type A B)
                ( |A+B|)
                ( f))
              ( mul-Commutative-Semigroup
                ( G)
                ( sum-finite-Commutative-Semigroup G A |A| (f ∘ inl))
                ( sum-finite-Commutative-Semigroup G B |B| (f ∘ inr))))
      in do
        cA ← is-finite-type-Finite-Type A
        cB ← is-finite-type-Finite-Type B
        ( eq-sum-finite-sum-count-Commutative-Semigroup
            ( G)
            ( coproduct-Finite-Type A B)
            ( |A+B|)
            ( count-coproduct cA cB)
            ( f) ∙
          distributive-sum-coproduct-count-Commutative-Semigroup
            ( G)
            ( type-Finite-Type A)
            ( |A|)
            ( type-Finite-Type B)
            ( |B|)
            ( |A+B|)
            ( cA)
            ( cB)
            ( f) ∙
          ap-mul-Commutative-Semigroup G
            ( inv
              ( eq-sum-finite-sum-count-Commutative-Semigroup
                ( G)
                ( A)
                ( |A|)
                ( cA)
                ( f ∘ inl)))
            ( inv
              ( eq-sum-finite-sum-count-Commutative-Semigroup
                ( G)
                ( B)
                ( |B|)
                ( cB)
                ( f ∘ inr))))
```
