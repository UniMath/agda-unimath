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

open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.iterating-automorphisms
open import foundation.sets
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-groups

open import structured-types.initial-pointed-type-equipped-with-automorphism
open import structured-types.pointed-types-equipped-with-automorphisms
```

</details>

## Idea

A group `F` equipped with an element `x : F` is said to satisfy the universal property of the free group with one generator if for every group `G` the map

```md
  type-hom-Group F G → type-Group G
```

given by `h ↦ h x` is an equivalence. The group of integers is a free group with one generator.

## Definitions

```agda
is-free-group-with-one-generator :
  {l1 : Level} (l2 : Level) (F : Group l1) (x : type-Group F) →
  UU (l1 ⊔ lsuc l2)
is-free-group-with-one-generator l2 F x =
  (G : Group l2) → is-equiv (λ (h : type-hom-Group F G) → map-hom-Group F G h x)
```

## Properties

### The group of integers is the free group with one generator

```agda
module _
  {l : Level} (G : Group l) (g : type-Group G)
  where

  generalized-map-hom-free-group-with-one-generator-ℤ :
    ℤ → type-Group G → type-Group G
  generalized-map-hom-free-group-with-one-generator-ℤ k =
    map-iterate-automorphism-ℤ k (equiv-mul-Group G g)

  associative-generalized-map-hom-free-group-with-one-generator-ℤ :
    (k : ℤ) (h1 h2 : type-Group G) →
    generalized-map-hom-free-group-with-one-generator-ℤ k (mul-Group G h1 h2) ＝
    mul-Group G (generalized-map-hom-free-group-with-one-generator-ℤ k h1) h2
  associative-generalized-map-hom-free-group-with-one-generator-ℤ
    ( inl zero-ℕ) h1 h2 =
    inv (associative-mul-Group G (inv-Group G g) h1 h2)
  associative-generalized-map-hom-free-group-with-one-generator-ℤ
    ( inl (succ-ℕ x)) h1 h2 =
    ( ap
      ( mul-Group G (inv-Group G g))
      ( associative-generalized-map-hom-free-group-with-one-generator-ℤ
        ( inl x)
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G
        ( inv-Group G g)
        ( generalized-map-hom-free-group-with-one-generator-ℤ (inl x) h1)
        ( h2)))
  associative-generalized-map-hom-free-group-with-one-generator-ℤ
    ( inr (inl star)) h1 h2 =
    refl
  associative-generalized-map-hom-free-group-with-one-generator-ℤ
    ( inr (inr zero-ℕ)) h1 h2 =
    inv (associative-mul-Group G g h1 h2)
  associative-generalized-map-hom-free-group-with-one-generator-ℤ
    ( inr (inr (succ-ℕ x))) h1 h2 =
    ( ap
      ( mul-Group G g)
      ( associative-generalized-map-hom-free-group-with-one-generator-ℤ
        ( inr (inr x))
        ( h1)
        ( h2))) ∙
    ( inv
      ( associative-mul-Group G g
        ( generalized-map-hom-free-group-with-one-generator-ℤ (inr (inr x)) h1)
        ( h2)))

  map-hom-free-group-with-one-generator-ℤ : ℤ → type-Group G
  map-hom-free-group-with-one-generator-ℤ k =
    generalized-map-hom-free-group-with-one-generator-ℤ k (unit-Group G)

  preserves-unit-hom-free-group-with-one-generator-ℤ :
    map-hom-free-group-with-one-generator-ℤ zero-ℤ ＝ unit-Group G
  preserves-unit-hom-free-group-with-one-generator-ℤ =
    preserves-point-map-ℤ-Pointed-Type-With-Aut
      ( pointed-type-with-aut-Group G g)

  preserves-mul-map-hom-free-group-with-one-generator-ℤ :
    (x y : ℤ) →
    ( map-hom-free-group-with-one-generator-ℤ (add-ℤ x y)) ＝
    ( mul-Group G
      ( map-hom-free-group-with-one-generator-ℤ x)
      ( map-hom-free-group-with-one-generator-ℤ y))
  preserves-mul-map-hom-free-group-with-one-generator-ℤ x y =
    ( iterate-automorphism-add-ℤ x y (equiv-mul-Group G g) (unit-Group G)) ∙
    ( ( ap
        ( generalized-map-hom-free-group-with-one-generator-ℤ x)
        ( inv (left-unit-law-mul-Group G
          ( map-hom-free-group-with-one-generator-ℤ y)))) ∙
      ( associative-generalized-map-hom-free-group-with-one-generator-ℤ x
        ( unit-Group G)
        ( map-hom-free-group-with-one-generator-ℤ y)))

  hom-free-group-with-one-generator-ℤ : type-hom-Group ℤ-Group G
  pr1 hom-free-group-with-one-generator-ℤ =
    map-hom-free-group-with-one-generator-ℤ
  pr2 hom-free-group-with-one-generator-ℤ =
    preserves-mul-map-hom-free-group-with-one-generator-ℤ

  htpy-hom-free-group-with-one-generator-ℤ :
    (h : type-hom-Group ℤ-Group G) → map-hom-Group ℤ-Group G h one-ℤ ＝ g →
    htpy-hom-Group ℤ-Group G hom-free-group-with-one-generator-ℤ h
  htpy-hom-free-group-with-one-generator-ℤ h p =
    htpy-map-ℤ-Pointed-Type-With-Aut
      ( pair (pointed-type-Group G) (equiv-mul-Group G g))
      ( pair
        ( map-hom-Group ℤ-Group G h)
        ( pair
          ( preserves-unit-hom-Group ℤ-Group G h)
          ( λ x →
            ( ap
              ( map-hom-Group ℤ-Group G h)
              ( is-add-one-succ-ℤ x)) ∙
            ( ( preserves-mul-hom-Group ℤ-Group G h one-ℤ x) ∙
              ( ap ( mul-Group' G (map-hom-Group ℤ-Group G h x)) p)))))

  is-contr-total-hom-free-group-with-one-generator-ℤ :
    is-contr
      ( Σ ( type-hom-Group ℤ-Group G)
          ( λ h → map-hom-Group ℤ-Group G h one-ℤ ＝ g))
  pr1 (pr1 is-contr-total-hom-free-group-with-one-generator-ℤ) =
    hom-free-group-with-one-generator-ℤ
  pr2 (pr1 is-contr-total-hom-free-group-with-one-generator-ℤ) =
    right-unit-law-mul-Group G g
  pr2 is-contr-total-hom-free-group-with-one-generator-ℤ (pair h p) =
    eq-type-subtype
      ( λ f → Id-Prop (set-Group G) (map-hom-Group ℤ-Group G f one-ℤ) g)
      ( eq-htpy-hom-Group ℤ-Group G
        ( htpy-hom-free-group-with-one-generator-ℤ h p))

is-hom-free-group-with-one-generator-ℤ :
  {l : Level} → is-free-group-with-one-generator l ℤ-Group one-ℤ
is-hom-free-group-with-one-generator-ℤ G =
  is-equiv-is-contr-map (is-contr-total-hom-free-group-with-one-generator-ℤ G)
```
