# Binary relations

```agda
module foundation.binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A **binary relation** on a type `A` is a family of types `R x y` depending on
two variables `x y : A`. In the special case where each `R x y` is a
[proposition](foundation-core.propositions.md), we say that the relation is
valued in propositions. Thus, we take a general relation to mean a
_proof-relevant_ relation.

## Definition

### Relations valued in types

```agda
Relation : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
Relation l A = A → A → UU l

total-space-Relation :
  {l1 l : Level} {A : UU l1} → Relation l A → UU (l1 ⊔ l)
total-space-Relation {A = A} R = Σ (A × A) λ (a , a') → R a a'
```

### Relations valued in propositions

```agda
Relation-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Relation-Prop l A = A → A → Prop l

type-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} → Relation-Prop l2 A → Relation l2 A
type-Relation-Prop R x y = pr1 (R x y)

is-prop-type-Relation-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A) →
  (x y : A) → is-prop (type-Relation-Prop R x y)
is-prop-type-Relation-Prop R x y = pr2 (R x y)

total-space-Relation-Prop :
  {l : Level} {l1 : Level} {A : UU l1} → Relation-Prop l A → UU (l ⊔ l1)
total-space-Relation-Prop {A = A} R =
  Σ (A × A) λ (a , a') → type-Relation-Prop R a a'
```

## Specifications of properties of binary relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Relation l2 A)
  where

  is-reflexive : UU (l1 ⊔ l2)
  is-reflexive = (x : A) → R x x

  is-symmetric : UU (l1 ⊔ l2)
  is-symmetric = (x y : A) → R x y → R y x

  is-transitive : UU (l1 ⊔ l2)
  is-transitive = (x y z : A) → R y z → R x y → R x z

  is-antisymmetric : UU (l1 ⊔ l2)
  is-antisymmetric = (x y : A) → R x y → R y x → x ＝ y

module _
  {l1 l2 : Level} {A : UU l1} (R : Relation-Prop l2 A)
  where

  is-reflexive-Relation-Prop : UU (l1 ⊔ l2)
  is-reflexive-Relation-Prop = is-reflexive (type-Relation-Prop R)

  is-prop-is-reflexive-Relation-Prop : is-prop is-reflexive-Relation-Prop
  is-prop-is-reflexive-Relation-Prop =
    is-prop-Π (λ x → is-prop-type-Relation-Prop R x x)

  is-symmetric-Relation-Prop : UU (l1 ⊔ l2)
  is-symmetric-Relation-Prop = is-symmetric (type-Relation-Prop R)

  is-prop-is-symmetric-Relation-Prop : is-prop is-symmetric-Relation-Prop
  is-prop-is-symmetric-Relation-Prop =
    is-prop-iterated-Π 3
      ( λ x y r → is-prop-type-Relation-Prop R y x)

  is-transitive-Relation-Prop : UU (l1 ⊔ l2)
  is-transitive-Relation-Prop = is-transitive (type-Relation-Prop R)

  is-prop-is-transitive-Relation-Prop : is-prop is-transitive-Relation-Prop
  is-prop-is-transitive-Relation-Prop =
    is-prop-iterated-Π 3
      ( λ x y z →
        is-prop-function-type
          ( is-prop-function-type (is-prop-type-Relation-Prop R x z)))

  is-antisymmetric-Relation-Prop : UU (l1 ⊔ l2)
  is-antisymmetric-Relation-Prop = is-antisymmetric (type-Relation-Prop R)
```

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
      ( λ x P → (y : A) → R x y ≃ P y)
      ( λ x →
        is-torsorial-Eq-Π
          ( λ y P → R x y ≃ P)
          ( λ y → is-torsorial-equiv (R x y)))

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
    is-torsorial-Eq-Π
      ( λ x P → has-same-elements-subtype (R x) P)
      ( λ x → is-torsorial-has-same-elements-subtype (R x))

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

## See also

- [Large binary relations](foundation.large-binary-relations.md)
