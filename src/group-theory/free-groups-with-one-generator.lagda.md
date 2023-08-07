# Free groups with one generator

```agda
module group-theory.free-groups-with-one-generator where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.group-of-integers
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups

open import structured-types.initial-pointed-type-equipped-with-automorphism
```

</details>

## Idea

A group `F` equipped with an element `x : F` is said to satisfy the universal
property of the free group with one generator if for every group `G` the map

```text
  type-hom-Group F G → type-Group G
```

given by `h ↦ h x` is an equivalence. The group of integers is a free group with
one generator.

## Definitions

```agda
is-free-group-with-one-generator :
  {l1 : Level} (F : Group l1) (x : type-Group F) → UUω
is-free-group-with-one-generator F x =
  {l2 : Level} (G : Group l2) →
  is-equiv (λ (h : type-hom-Group F G) → map-hom-Group F G h x)
```

## Properties

### The group of integers is the free group with one generator

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  generalized-map-hom-Group-ℤ :
    ℤ → type-Group G → type-Group G
  generalized-map-hom-Group-ℤ k =
    map-iterate-automorphism-ℤ k (equiv-mul-Group G g)

  associative-generalized-map-hom-Group-ℤ :
    (k : ℤ) (h1 h2 : type-Group G) →
    generalized-map-hom-Group-ℤ k (mul-Group G h1 h2) ＝
    mul-Group G (generalized-map-hom-Group-ℤ k h1) h2
  associative-generalized-map-hom-Group-ℤ
    ( inl zero-ℕ) h1 h2 =
    inv (associative-mul-Group G (inv-Group G g) h1 h2)
  associative-generalized-map-hom-Group-ℤ
    ( inl (succ-ℕ x)) h1 h2 =
    ( ap
      ( mul-Group G (inv-Group G g))
      ( associative-generalized-map-hom-Group-ℤ
        ( inl x)
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G
        ( inv-Group G g)
        ( generalized-map-hom-Group-ℤ (inl x) h1)
        ( h2)))
  associative-generalized-map-hom-Group-ℤ
    ( inr (inl star)) h1 h2 =
    refl
  associative-generalized-map-hom-Group-ℤ
    ( inr (inr zero-ℕ)) h1 h2 =
    inv (associative-mul-Group G g h1 h2)
  associative-generalized-map-hom-Group-ℤ
    ( inr (inr (succ-ℕ x))) h1 h2 =
    ( ap
      ( mul-Group G g)
      ( associative-generalized-map-hom-Group-ℤ
        ( inr (inr x))
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G g
        ( generalized-map-hom-Group-ℤ (inr (inr x)) h1)
        ( h2)))

  map-hom-Group-ℤ : ℤ → type-Group G
  map-hom-Group-ℤ k =
    generalized-map-hom-Group-ℤ k (unit-Group G)

  preserves-unit-hom-Group-ℤ :
    map-hom-Group-ℤ zero-ℤ ＝ unit-Group G
  preserves-unit-hom-Group-ℤ =
    preserves-point-map-ℤ-Pointed-Type-With-Aut
      ( pointed-type-with-aut-Group G g)

  preserves-mul-map-hom-Group-ℤ :
    (x y : ℤ) →
    ( map-hom-Group-ℤ (x +ℤ y)) ＝
    ( mul-Group G
      ( map-hom-Group-ℤ x)
      ( map-hom-Group-ℤ y))
  preserves-mul-map-hom-Group-ℤ x y =
    ( iterate-automorphism-add-ℤ x y (equiv-mul-Group G g) (unit-Group G)) ∙
    ( ( ap
        ( generalized-map-hom-Group-ℤ x)
        ( inv (left-unit-law-mul-Group G
          ( map-hom-Group-ℤ y)))) ∙
      ( associative-generalized-map-hom-Group-ℤ x
        ( unit-Group G)
        ( map-hom-Group-ℤ y)))

  hom-Group-ℤ : type-hom-Group ℤ-Group G
  pr1 hom-Group-ℤ =
    map-hom-Group-ℤ
  pr2 hom-Group-ℤ =
    preserves-mul-map-hom-Group-ℤ

  htpy-hom-Group-ℤ :
    (h : type-hom-Group ℤ-Group G) → map-hom-Group ℤ-Group G h one-ℤ ＝ g →
    htpy-hom-Group ℤ-Group G hom-Group-ℤ h
  htpy-hom-Group-ℤ h p =
    htpy-map-ℤ-Pointed-Type-With-Aut
      ( pair (pointed-type-Group G) (equiv-mul-Group G g))
      ( pair
        ( map-hom-Group ℤ-Group G h)
        ( pair
          ( preserves-unit-hom-Group ℤ-Group G h)
          ( λ x →
            ( ap
              ( map-hom-Group ℤ-Group G h)
              ( is-left-add-one-succ-ℤ x)) ∙
            ( ( preserves-mul-hom-Group ℤ-Group G h one-ℤ x) ∙
              ( ap ( mul-Group' G (map-hom-Group ℤ-Group G h x)) p)))))

  is-contr-total-hom-Group-ℤ :
    is-contr
      ( Σ ( type-hom-Group ℤ-Group G)
          ( λ h → map-hom-Group ℤ-Group G h one-ℤ ＝ g))
  pr1 (pr1 is-contr-total-hom-Group-ℤ) =
    hom-Group-ℤ
  pr2 (pr1 is-contr-total-hom-Group-ℤ) =
    right-unit-law-mul-Group G g
  pr2 is-contr-total-hom-Group-ℤ (pair h p) =
    eq-type-subtype
      ( λ f → Id-Prop (set-Group G) (map-hom-Group ℤ-Group G f one-ℤ) g)
      ( eq-htpy-hom-Group ℤ-Group G
        ( htpy-hom-Group-ℤ h p))

abstract
  is-free-group-with-one-generator-ℤ :
    is-free-group-with-one-generator ℤ-Group one-ℤ
  is-free-group-with-one-generator-ℤ G =
    is-equiv-is-contr-map (is-contr-total-hom-Group-ℤ G)
```
