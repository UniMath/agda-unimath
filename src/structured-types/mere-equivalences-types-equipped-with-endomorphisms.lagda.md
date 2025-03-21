# Mere equivalences of types equipped with endomorphisms

```agda
module structured-types.mere-equivalences-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import structured-types.equivalences-types-equipped-with-endomorphisms
open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Definition

### Mere equivalences of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level}
  (X : Type-With-Endomorphism l1)
  (Y : Type-With-Endomorphism l2)
  where

  mere-equiv-prop-Type-With-Endomorphism : Prop (l1 ⊔ l2)
  mere-equiv-prop-Type-With-Endomorphism =
    trunc-Prop (equiv-Type-With-Endomorphism X Y)

  mere-equiv-Type-With-Endomorphism : UU (l1 ⊔ l2)
  mere-equiv-Type-With-Endomorphism =
    type-Prop mere-equiv-prop-Type-With-Endomorphism

  is-prop-mere-equiv-Type-With-Endomorphism :
    is-prop mere-equiv-Type-With-Endomorphism
  is-prop-mere-equiv-Type-With-Endomorphism =
    is-prop-type-Prop mere-equiv-prop-Type-With-Endomorphism
```

### Refleivity of mere equivalences of types equipped with endomorphisms

```agda
module _
  {l1 : Level} (X : Type-With-Endomorphism l1)
  where

  refl-mere-equiv-Type-With-Endomorphism : mere-equiv-Type-With-Endomorphism X X
  refl-mere-equiv-Type-With-Endomorphism =
    unit-trunc-Prop (id-equiv-Type-With-Endomorphism X)
```

### Components of the universe of types equipped with endomorphisms

```agda
module _
  {l1 : Level} (X : Type-With-Endomorphism l1)
  where

  Component-Type-With-Endomorphism : UU (lsuc l1)
  Component-Type-With-Endomorphism =
    Σ (Type-With-Endomorphism l1) (mere-equiv-Type-With-Endomorphism X)

  endo-Component-Type-With-Endomorphism :
    Component-Type-With-Endomorphism → Type-With-Endomorphism l1
  endo-Component-Type-With-Endomorphism = pr1

  type-Component-Type-With-Endomorphism :
    Component-Type-With-Endomorphism → UU l1
  type-Component-Type-With-Endomorphism =
    pr1 ∘ endo-Component-Type-With-Endomorphism

  endomorphism-Component-Type-With-Endomorphism :
    (T : Component-Type-With-Endomorphism) →
    type-Component-Type-With-Endomorphism T →
    type-Component-Type-With-Endomorphism T
  endomorphism-Component-Type-With-Endomorphism T =
    pr2 (endo-Component-Type-With-Endomorphism T)

  mere-equiv-Component-Type-With-Endomorphism :
    (T : Component-Type-With-Endomorphism) →
    mere-equiv-Type-With-Endomorphism X
      ( endo-Component-Type-With-Endomorphism T)
  mere-equiv-Component-Type-With-Endomorphism T = pr2 T

  canonical-Component-Type-With-Endomorphism : Component-Type-With-Endomorphism
  pr1 canonical-Component-Type-With-Endomorphism = X
  pr2 canonical-Component-Type-With-Endomorphism =
    refl-mere-equiv-Type-With-Endomorphism X
```

### Equivalences of types equipped with an endomorphism in a given component

```agda
module _
  {l1 : Level} (X : Type-With-Endomorphism l1)
  where

  equiv-Component-Type-With-Endomorphism :
    (T S : Component-Type-With-Endomorphism X) → UU l1
  equiv-Component-Type-With-Endomorphism T S =
    equiv-Type-With-Endomorphism
      ( endo-Component-Type-With-Endomorphism X T)
      ( endo-Component-Type-With-Endomorphism X S)

  id-equiv-Component-Type-With-Endomorphism :
    ( T : Component-Type-With-Endomorphism X) →
    equiv-Component-Type-With-Endomorphism T T
  id-equiv-Component-Type-With-Endomorphism T =
    id-equiv-Type-With-Endomorphism (endo-Component-Type-With-Endomorphism X T)

  equiv-eq-Component-Type-With-Endomorphism :
    (T S : Component-Type-With-Endomorphism X) →
    T ＝ S → equiv-Component-Type-With-Endomorphism T S
  equiv-eq-Component-Type-With-Endomorphism T .T refl =
    id-equiv-Component-Type-With-Endomorphism T

  is-torsorial-equiv-Component-Type-With-Endomorphism :
    is-torsorial
      ( equiv-Component-Type-With-Endomorphism
        ( canonical-Component-Type-With-Endomorphism X))
  is-torsorial-equiv-Component-Type-With-Endomorphism =
    is-torsorial-Eq-subtype
      ( is-torsorial-equiv-Type-With-Endomorphism X)
      ( λ Y → is-prop-type-trunc-Prop)
      ( X)
      ( id-equiv-Type-With-Endomorphism X)
      ( refl-mere-equiv-Type-With-Endomorphism X)

  is-equiv-equiv-eq-Component-Type-With-Endomorphism :
    (T : Component-Type-With-Endomorphism X) →
    is-equiv
      ( equiv-eq-Component-Type-With-Endomorphism
        ( canonical-Component-Type-With-Endomorphism X)
        ( T))
  is-equiv-equiv-eq-Component-Type-With-Endomorphism =
    fundamental-theorem-id
      ( is-torsorial-equiv-Component-Type-With-Endomorphism)
      ( equiv-eq-Component-Type-With-Endomorphism
        ( canonical-Component-Type-With-Endomorphism X))
```
