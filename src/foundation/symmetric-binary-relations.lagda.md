# Symmetric binary relations

```agda
module foundation.symmetric-binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-binary-relations
open import foundation.symmetric-operations
open import foundation.transport-along-identifications
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
Symmetric-Relation :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
Symmetric-Relation l2 A = symmetric-operation A (UU l2)
```

### Action on symmetries of symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Symmetric-Relation l2 A)
  where

  abstract
    equiv-tr-Symmetric-Relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R p ≃ R q
    equiv-tr-Symmetric-Relation p =
      ind-Eq-unordered-pair p (λ q e → R p ≃ R q) id-equiv

    compute-refl-equiv-tr-Symmetric-Relation :
      (p : unordered-pair A) →
      equiv-tr-Symmetric-Relation p p (refl-Eq-unordered-pair p) ＝
      id-equiv
    compute-refl-equiv-tr-Symmetric-Relation p =
      compute-refl-ind-Eq-unordered-pair p (λ q e → R p ≃ R q) id-equiv

    htpy-compute-refl-equiv-tr-Symmetric-Relation :
      (p : unordered-pair A) →
      htpy-equiv
        ( equiv-tr-Symmetric-Relation p p (refl-Eq-unordered-pair p))
        ( id-equiv)
    htpy-compute-refl-equiv-tr-Symmetric-Relation p =
      htpy-eq-equiv (compute-refl-equiv-tr-Symmetric-Relation p)

  abstract
    tr-Symmetric-Relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R p → R q
    tr-Symmetric-Relation p q e =
      map-equiv (equiv-tr-Symmetric-Relation p q e)

    tr-inv-Symmetric-Relation :
      (p q : unordered-pair A) → Eq-unordered-pair p q → R q → R p
    tr-inv-Symmetric-Relation p q e =
      map-inv-equiv (equiv-tr-Symmetric-Relation p q e)

    is-section-tr-inv-Symmetric-Relation :
      (p q : unordered-pair A) (e : Eq-unordered-pair p q) →
      tr-Symmetric-Relation p q e ∘
      tr-inv-Symmetric-Relation p q e ~
      id
    is-section-tr-inv-Symmetric-Relation p q e =
      is-section-map-inv-equiv (equiv-tr-Symmetric-Relation p q e)

    is-retraction-tr-inv-Symmetric-Relation :
      (p q : unordered-pair A) (e : Eq-unordered-pair p q) →
      tr-inv-Symmetric-Relation p q e ∘
      tr-Symmetric-Relation p q e ~
      id
    is-retraction-tr-inv-Symmetric-Relation p q e =
      is-retraction-map-inv-equiv (equiv-tr-Symmetric-Relation p q e)

    compute-refl-tr-Symmetric-Relation :
      (p : unordered-pair A) →
      tr-Symmetric-Relation p p (refl-Eq-unordered-pair p) ＝ id
    compute-refl-tr-Symmetric-Relation p =
      ap map-equiv (compute-refl-equiv-tr-Symmetric-Relation p)

    htpy-compute-refl-tr-Symmetric-Relation :
      (p : unordered-pair A) →
      tr-Symmetric-Relation p p (refl-Eq-unordered-pair p) ~ id
    htpy-compute-refl-tr-Symmetric-Relation p =
      htpy-eq (compute-refl-tr-Symmetric-Relation p)
```

### The underlying binary relation of a symmetric binary relation

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Symmetric-Relation l2 A)
  where

  relation-Symmetric-Relation : Relation l2 A
  relation-Symmetric-Relation x y = R (standard-unordered-pair x y)

  equiv-symmetric-relation-Symmetric-Relation :
    {x y : A} →
    relation-Symmetric-Relation x y ≃
    relation-Symmetric-Relation y x
  equiv-symmetric-relation-Symmetric-Relation {x} {y} =
    equiv-tr-Symmetric-Relation R
      ( standard-unordered-pair x y)
      ( standard-unordered-pair y x)
      ( swap-standard-unordered-pair x y)

  symmetric-relation-Symmetric-Relation :
    {x y : A} →
    relation-Symmetric-Relation x y →
    relation-Symmetric-Relation y x
  symmetric-relation-Symmetric-Relation =
    map-equiv equiv-symmetric-relation-Symmetric-Relation
```

### The forgetful functor from binary relations to symmetric binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  symmetric-relation-Relation : Symmetric-Relation l2 A
  symmetric-relation-Relation p =
    Σ ( type-unordered-pair p)
      ( λ i →
        R (element-unordered-pair p i) (other-element-unordered-pair p i))

  unit-symmetric-relation-Relation :
    (x y : A) → R x y →
    relation-Symmetric-Relation symmetric-relation-Relation x y
  pr1 (unit-symmetric-relation-Relation x y r) = zero-Fin 1
  pr2 (unit-symmetric-relation-Relation x y r) =
    tr
      ( R x)
      ( inv (compute-other-element-standard-unordered-pair x y (zero-Fin 1)))
      ( r)
```

### Morphisms of symmetric binary relations

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  hom-Symmetric-Relation :
    Symmetric-Relation l2 A → Symmetric-Relation l3 A →
    UU (lsuc lzero ⊔ l1 ⊔ l2 ⊔ l3)
  hom-Symmetric-Relation R S =
    (p : unordered-pair A) → R p → S p

  hom-relation-hom-Symmetric-Relation :
    (R : Symmetric-Relation l2 A) (S : Symmetric-Relation l3 A) →
    hom-Symmetric-Relation R S →
    hom-Relation
      ( relation-Symmetric-Relation R)
      ( relation-Symmetric-Relation S)
  hom-relation-hom-Symmetric-Relation R S f x y =
    f (standard-unordered-pair x y)
```
