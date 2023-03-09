# Binary relations

```agda
module foundation.binary-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.equality-dependent-function-types
open import foundation.subtypes
open import foundation.univalence

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.universe-levels
```

</details>

## Idea

A binary relation on a type `A` is a family of types `R x y` depending on two variables `x y : A`. In the special case where each `R x y` is a proposition, we say that the relation is valued in propositions.

## Definition

### Type-valued relations

```agda
Rel : {l1 : Level} (l : Level) (A : UU l1) → UU (l1 ⊔ lsuc l)
Rel l A = A → A → UU l

total-space-Rel : {l1 l : Level} {A : UU l1}
        → Rel l A → UU (l1 ⊔ l)
total-space-Rel {A = A} R = Σ (A × A) λ (pair a a') → R a a'
```

### Relations valued in propositions

```agda
Rel-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU ((lsuc l) ⊔ l1)
Rel-Prop l A = A → (A → Prop l)

type-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) → A → A → UU l2
type-Rel-Prop R x y = pr1 (R x y)

abstract
  is-prop-type-Rel-Prop :
    {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
    (x y : A) → is-prop (type-Rel-Prop R x y)
  is-prop-type-Rel-Prop R x y = pr2 (R x y)

total-space-Rel-Prop : {l : Level} {l1 : Level} {A : UU l1}
             → Rel-Prop l A → UU (l ⊔ l1)
total-space-Rel-Prop {A = A} R = Σ (A × A) λ (pair a a') → type-Rel-Prop R a a'
```

## Specifications of properties of binary relations

```agda
is-reflexive : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-reflexive {A = A} R = (x : A) → R x x

is-symmetric : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-symmetric {A = A} R = (x y : A) → R x y → R y x

is-transitive : {l1 l2 : Level} {A : UU l1} → Rel l2 A → UU (l1 ⊔ l2)
is-transitive {A = A} R = (x y z : A) → R x y → R y z → R x z

is-reflexive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-reflexive-Rel-Prop {A = A} R =
  {x : A} → type-Rel-Prop R x x

is-prop-is-reflexive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
  is-prop (is-reflexive-Rel-Prop R)
is-prop-is-reflexive-Rel-Prop R =
  is-prop-Π' (λ x → is-prop-type-Rel-Prop R x x)

is-symmetric-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-symmetric-Rel-Prop {A = A} R =
  {x y : A} → type-Rel-Prop R x y → type-Rel-Prop R y x

is-prop-is-symmetric-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
  is-prop (is-symmetric-Rel-Prop R)
is-prop-is-symmetric-Rel-Prop R =
  is-prop-Π'
    ( λ x →
      is-prop-Π' (λ y → is-prop-function-type (is-prop-type-Rel-Prop R y x)))

is-transitive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} → Rel-Prop l2 A → UU (l1 ⊔ l2)
is-transitive-Rel-Prop {A = A} R =
  {x y z : A} → type-Rel-Prop R x y → type-Rel-Prop R y z → type-Rel-Prop R x z

is-prop-is-transitive-Rel-Prop :
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A) →
  is-prop (is-transitive-Rel-Prop R)
is-prop-is-transitive-Rel-Prop R =
  is-prop-Π'
    ( λ x →
      is-prop-Π'
        ( λ y →
          is-prop-Π'
            ( λ z →
              is-prop-function-type
                ( is-prop-function-type (is-prop-type-Rel-Prop R x z)))))
```

## Properties

### Characterization of equality of binary relations

```agda
equiv-Rel :
  {l1 l2 l3 : Level} {A : UU l1} → Rel l2 A → Rel l3 A → UU (l1 ⊔ l2 ⊔ l3)
equiv-Rel {A = A} R S = (x y : A) → R x y ≃ S x y

module _
  {l1 l2 : Level} {A : UU l1} (R : Rel l2 A)
  where

  id-equiv-Rel : equiv-Rel R R
  id-equiv-Rel x y = id-equiv

  is-contr-total-equiv-Rel :
    is-contr (Σ (Rel l2 A) (equiv-Rel R))
  is-contr-total-equiv-Rel =
    is-contr-total-Eq-Π
      ( λ x P → (y : A) → R x y ≃ P y)
      ( λ x →
        is-contr-total-Eq-Π
          ( λ y P → R x y ≃ P)
          ( λ y → is-contr-total-equiv (R x y)))

  equiv-eq-Rel : (S : Rel l2 A) → (R ＝ S) → equiv-Rel R S
  equiv-eq-Rel .R refl = id-equiv-Rel

  is-equiv-equiv-eq-Rel : (S : Rel l2 A) → is-equiv (equiv-eq-Rel S)
  is-equiv-equiv-eq-Rel =
    fundamental-theorem-id is-contr-total-equiv-Rel equiv-eq-Rel

  extensionality-Rel : (S : Rel l2 A) → (R ＝ S) ≃ equiv-Rel R S
  pr1 (extensionality-Rel S) = equiv-eq-Rel S
  pr2 (extensionality-Rel S) = is-equiv-equiv-eq-Rel S

  eq-equiv-Rel : (S : Rel l2 A) → equiv-Rel R S → (R ＝ S)
  eq-equiv-Rel S = map-inv-equiv (extensionality-Rel S)
```

### Characterization of equality of prop-valued binary relations

```agda
relates-same-elements-Rel-Prop :
  {l1 l2 l3 : Level} {A : UU l1} (R : Rel-Prop l2 A) (S : Rel-Prop l3 A) →
  UU (l1 ⊔ l2 ⊔ l3)
relates-same-elements-Rel-Prop {A = A} R S =
  (x : A) → has-same-elements-subtype (R x) (S x)

module _
  {l1 l2 : Level} {A : UU l1} (R : Rel-Prop l2 A)
  where

  refl-relates-same-elements-Rel-Prop : relates-same-elements-Rel-Prop R R
  refl-relates-same-elements-Rel-Prop x = refl-has-same-elements-subtype (R x)

  is-contr-total-relates-same-elements-Rel-Prop :
    is-contr (Σ (Rel-Prop l2 A) (relates-same-elements-Rel-Prop R))
  is-contr-total-relates-same-elements-Rel-Prop =
    is-contr-total-Eq-Π
      ( λ x P → has-same-elements-subtype (R x) P)
      ( λ x → is-contr-total-has-same-elements-subtype (R x))

  relates-same-elements-eq-Rel-Prop :
    (S : Rel-Prop l2 A) → (R ＝ S) → relates-same-elements-Rel-Prop R S
  relates-same-elements-eq-Rel-Prop .R refl =
    refl-relates-same-elements-Rel-Prop

  is-equiv-relates-same-elements-eq-Rel-Prop :
    (S : Rel-Prop l2 A) → is-equiv (relates-same-elements-eq-Rel-Prop S)
  is-equiv-relates-same-elements-eq-Rel-Prop =
    fundamental-theorem-id
      is-contr-total-relates-same-elements-Rel-Prop
      relates-same-elements-eq-Rel-Prop

  extensionality-Rel-Prop :
    (S : Rel-Prop l2 A) → (R ＝ S) ≃ relates-same-elements-Rel-Prop R S
  pr1 (extensionality-Rel-Prop S) = relates-same-elements-eq-Rel-Prop S
  pr2 (extensionality-Rel-Prop S) = is-equiv-relates-same-elements-eq-Rel-Prop S

  eq-relates-same-elements-Rel-Prop :
    (S : Rel-Prop l2 A) → relates-same-elements-Rel-Prop R S → (R ＝ S)
  eq-relates-same-elements-Rel-Prop S =
    map-inv-equiv (extensionality-Rel-Prop S)
```
