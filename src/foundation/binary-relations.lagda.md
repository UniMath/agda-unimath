# Binary relations

```agda
module foundation.binary-relations where

open import foundation-core.binary-relations public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.iterated-dependent-product-types
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A {{#concept "binary relation" Agda=Relation}} on a type `A` is a family of types `R x y` depending on
two variables `x y : A`. In the special case where each `R x y` is a
[proposition](foundation-core.propositions.md), we say that the relation is
valued in propositions. Thus, we take a general relation to mean a
_proof-relevant_ relation.

## Properties

### Characterization of equality of binary relations

```agda
equiv-Relation :
  {l1 l2 l3 : Level} {A : UU l1} →
  Relation l2 A → Relation l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Relation {A = A} R S = (x y : A) → R x y ≃ S x y

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  id-equiv-Relation : equiv-Relation R R
  id-equiv-Relation x y = id-equiv

  is-torsorial-equiv-Relation :
    is-torsorial (equiv-Relation R)
  is-torsorial-equiv-Relation =
    is-torsorial-Eq-Π
      ( λ x → is-torsorial-Eq-Π (λ y → is-torsorial-equiv (R x y)))

  equiv-eq-Relation : (S : Relation l2 A) → (R ＝ S) → equiv-Relation R S
  equiv-eq-Relation .R refl = id-equiv-Relation

  is-equiv-equiv-eq-Relation :
    (S : Relation l2 A) → is-equiv (equiv-eq-Relation S)
  is-equiv-equiv-eq-Relation =
    fundamental-theorem-id is-torsorial-equiv-Relation equiv-eq-Relation

  extensionality-Relation : (S : Relation l2 A) → (R ＝ S) ≃ equiv-Relation R S
  pr1 (extensionality-Relation S) = equiv-eq-Relation S
  pr2 (extensionality-Relation S) = is-equiv-equiv-eq-Relation S

  eq-equiv-Relation : (S : Relation l2 A) → equiv-Relation R S → (R ＝ S)
  eq-equiv-Relation S = map-inv-equiv (extensionality-Relation S)
```

### Characterization of equality of prop-valued binary relations

```agda
relates-same-elements-Relation-Prop :
  {l1 l2 l3 : Level} {A : UU l1}
  (R : Relation-Prop l2 A) (S : Relation-Prop l3 A) →
  UU (l1 ⊔ l2 ⊔ l3)
relates-same-elements-Relation-Prop {A = A} R S =
  (x : A) → has-same-elements-subtype (R x) (S x)

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  refl-relates-same-elements-Relation-Prop :
    relates-same-elements-Relation-Prop R R
  refl-relates-same-elements-Relation-Prop x =
    refl-has-same-elements-subtype (R x)

  is-torsorial-relates-same-elements-Relation-Prop :
    is-torsorial (relates-same-elements-Relation-Prop R)
  is-torsorial-relates-same-elements-Relation-Prop =
    is-torsorial-Eq-Π (λ x → is-torsorial-has-same-elements-subtype (R x))

  relates-same-elements-eq-Relation-Prop :
    (S : Relation-Prop l2 A) →
    (R ＝ S) → relates-same-elements-Relation-Prop R S
  relates-same-elements-eq-Relation-Prop .R refl =
    refl-relates-same-elements-Relation-Prop

  is-equiv-relates-same-elements-eq-Relation-Prop :
    (S : Relation-Prop l2 A) →
    is-equiv (relates-same-elements-eq-Relation-Prop S)
  is-equiv-relates-same-elements-eq-Relation-Prop =
    fundamental-theorem-id
      is-torsorial-relates-same-elements-Relation-Prop
      relates-same-elements-eq-Relation-Prop

  extensionality-Relation-Prop :
    (S : Relation-Prop l2 A) →
    (R ＝ S) ≃ relates-same-elements-Relation-Prop R S
  pr1 (extensionality-Relation-Prop S) =
    relates-same-elements-eq-Relation-Prop S
  pr2 (extensionality-Relation-Prop S) =
    is-equiv-relates-same-elements-eq-Relation-Prop S

  eq-relates-same-elements-Relation-Prop :
    (S : Relation-Prop l2 A) →
    relates-same-elements-Relation-Prop R S → (R ＝ S)
  eq-relates-same-elements-Relation-Prop S =
    map-inv-equiv (extensionality-Relation-Prop S)
```

### Asymmetric relations are irreflexive

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-irreflexive-is-asymmetric : is-asymmetric R → is-irreflexive R
  is-irreflexive-is-asymmetric H x r = H x x r r
```

### Asymmetric relations are antisymmetric

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-antisymmetric-is-asymmetric : is-asymmetric R → is-antisymmetric R
  is-antisymmetric-is-asymmetric H x y r s = ex-falso (H x y r s)
```

## See also

- [Large binary relations](foundation.large-binary-relations.md)
