# Symmetric binary relations

```agda
{-# OPTIONS --allow-unsolved-metas #-}

module foundation.symmetric-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-equivalences-type-families
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.symmetric-operations
open import foundation.transport
open import foundation.universe-levels
open import foundation.unordered-pairs

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A **symmetric binary relation** on a type `A` is a type family `R` over the type
of [unordered pairs](foundation.unordered-pairs.md) of elements of `A`. Given a
symmetric binary relation `R` on `A` and an equivalence of unordered pairs
`p ＝ q`, we have `R p ≃ R q`. In particular, we have

```text
  R ({x,y}) ≃ R ({y,x})
```

for any two elements `x y : A`, where `{x,y}` is the _standard unordered pair_
consisting of `x` and `y`.

Note that a symmetric binary relation R on a type is just a
[symmetric operation](foundation.symmetric-operations.md) from `A` into a
universe `𝒰`.

## Definitions

### Symmetric binary relations

```agda
symmetric-binary-relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
symmetric-binary-relation l2 A = symmetric-operation A (UU l2)
```

### Action on symmetries of symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : symmetric-binary-relation l2 A)
  where

  abstract
    equiv-tr-symmetric-binary-relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R p ≃ R q
    equiv-tr-symmetric-binary-relation p =
      ind-Eq-unordered-pair p (λ q e → R p ≃ R q) id-equiv

    compute-refl-equiv-tr-symmetric-binary-relation :
      (p : unordered-pair A) →
      equiv-tr-symmetric-binary-relation p p (refl-Eq-unordered-pair p) ＝
      id-equiv
    compute-refl-equiv-tr-symmetric-binary-relation p =
      compute-refl-ind-Eq-unordered-pair p (λ q e → R p ≃ R q) id-equiv

    htpy-compute-refl-equiv-tr-symmetric-binary-relation :
      (p : unordered-pair A) →
      htpy-equiv
        ( equiv-tr-symmetric-binary-relation p p (refl-Eq-unordered-pair p))
        ( id-equiv)
    htpy-compute-refl-equiv-tr-symmetric-binary-relation p =
      htpy-eq-equiv (compute-refl-equiv-tr-symmetric-binary-relation p)

  abstract
    tr-symmetric-binary-relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R p → R q
    tr-symmetric-binary-relation p q e =
      map-equiv (equiv-tr-symmetric-binary-relation p q e)

    compute-refl-tr-symmetric-binary-relation :
      (p : unordered-pair A) →
      tr-symmetric-binary-relation p p (refl-Eq-unordered-pair p) ＝ id
    compute-refl-tr-symmetric-binary-relation p =
      ap map-equiv (compute-refl-equiv-tr-symmetric-binary-relation p)

    htpy-compute-refl-tr-symmetric-binary-relation :
      (p : unordered-pair A) →
      tr-symmetric-binary-relation p p (refl-Eq-unordered-pair p) ~ id
    htpy-compute-refl-tr-symmetric-binary-relation p =
      htpy-eq (compute-refl-tr-symmetric-binary-relation p)
```

### The underlying binary relation of a symmetric binary relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : symmetric-binary-relation l2 A)
  where

  rel-symmetric-binary-relation : Rel l2 A
  rel-symmetric-binary-relation x y = R (standard-unordered-pair x y)

  equiv-symmetric-rel-symmetric-binary-relation :
    {x y : A} →
    rel-symmetric-binary-relation x y ≃ rel-symmetric-binary-relation y x
  equiv-symmetric-rel-symmetric-binary-relation {x} {y} =
    equiv-tr-symmetric-binary-relation R
      ( standard-unordered-pair x y)
      ( standard-unordered-pair y x)
      ( swap-standard-unordered-pair x y)

  symmetric-rel-symmetric-binary-relation :
    {x y : A} →
    rel-symmetric-binary-relation x y → rel-symmetric-binary-relation y x
  symmetric-rel-symmetric-binary-relation =
    map-equiv equiv-symmetric-rel-symmetric-binary-relation
```

### The forgetful functor from binary relations to symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Rel l2 A)
  where

  symmetric-binary-relation-Rel : symmetric-binary-relation l2 A
  symmetric-binary-relation-Rel p =
    Σ ( type-unordered-pair p)
      ( λ i →
        R (element-unordered-pair p i) (other-element-unordered-pair p i))

  unit-symmetric-binary-relation-Rel :
    (x y : A) →
    R x y → rel-symmetric-binary-relation symmetric-binary-relation-Rel x y
  pr1 (unit-symmetric-binary-relation-Rel x y r) = zero-Fin 1
  pr2 (unit-symmetric-binary-relation-Rel x y r) =
    tr
      ( R x)
      ( inv (compute-other-element-standard-unordered-pair x y (zero-Fin 1)))
      ( r)
```

### The symmetric core of a binary relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Rel l2 A)
  where

  symmetric-core-Rel : symmetric-binary-relation l2 A
  symmetric-core-Rel p =
    (i : type-unordered-pair p) →
    R (element-unordered-pair p i) (other-element-unordered-pair p i)

  counit-symmetric-core-Rel :
    {x y : A} →
    rel-symmetric-binary-relation symmetric-core-Rel x y → R x y
  counit-symmetric-core-Rel {x} {y} r =
    tr
      ( R x)
      ( compute-other-element-standard-unordered-pair x y (zero-Fin 1))
      ( r (zero-Fin 1))
```

### Morphisms of symmetric binary relations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  hom-symmetric-binary-relation :
    symmetric-binary-relation l2 A → symmetric-binary-relation l3 A →
    UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3)
  hom-symmetric-binary-relation R S =
    (p : unordered-pair A) → R p → S p

  hom-rel-hom-symmetric-binary-relation :
    (R : symmetric-binary-relation l2 A) (S : symmetric-binary-relation l3 A) →
    hom-symmetric-binary-relation R S →
    hom-Rel
      ( rel-symmetric-binary-relation R)
      ( rel-symmetric-binary-relation S)
  hom-rel-hom-symmetric-binary-relation R S f x y =
    f (standard-unordered-pair x y)
```

## Properties

### The universal property of the symmetric core of a binary relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Rel l2 A)
  (S : symmetric-binary-relation l3 A)
  where

  map-universal-property-symmetric-core-Rel :
    hom-symmetric-binary-relation S (symmetric-core-Rel R) →
    hom-Rel (rel-symmetric-binary-relation S) R
  map-universal-property-symmetric-core-Rel f x y s =
    counit-symmetric-core-Rel R (f (standard-unordered-pair x y) s)

  map-inv-universal-property-symmetric-core-Rel :
    hom-Rel (rel-symmetric-binary-relation S) R →
    hom-symmetric-binary-relation S (symmetric-core-Rel R)
  map-inv-universal-property-symmetric-core-Rel f p s i =
    f ( element-unordered-pair p i)
      ( other-element-unordered-pair p i)
      ( tr-symmetric-binary-relation S
        ( p)
        ( standard-unordered-pair
          ( element-unordered-pair p i)
          ( other-element-unordered-pair p i))
        ( inv-Eq-unordered-pair
          ( standard-unordered-pair
            ( element-unordered-pair p i)
            ( other-element-unordered-pair p i))
          ( p)
          ( compute-standard-unordered-pair-element-unordered-pair p i))
        ( s))

  is-section-map-inv-universal-property-symmetric-core-Rel :
    ( map-universal-property-symmetric-core-Rel ∘
      map-inv-universal-property-symmetric-core-Rel) ~ id
  is-section-map-inv-universal-property-symmetric-core-Rel f =
    eq-htpy
      ( λ p →
        eq-htpy
          ( λ s →
            eq-htpy
              ( λ i →
                {!!})))
```
