# Mere equivalences of types equipped with endomorphisms

```agda
module structured-types.mere-equivalences-types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import structured-types.equivalences-types-equipped-with-endomorphisms
open import structured-types.types-equipped-with-endomorphisms
```

</details>

## Definition

### Mere equivalences of types equipped with endomorphisms

```agda
module _
  {l1 l2 : Level} (X : Endo l1) (Y : Endo l2)
  where

  mere-equiv-Endo : UU (l1 ⊔ l2)
  mere-equiv-Endo = type-trunc-Prop (equiv-Endo X Y)
```

### Refleivity of mere equivalences of types equipped with endomorphisms

```agda
module _
  {l1 : Level} (X : Endo l1)
  where

  refl-mere-equiv-Endo : mere-equiv-Endo X X
  refl-mere-equiv-Endo = unit-trunc-Prop (id-equiv-Endo X)
```

### Components of the universe of types equipped with endomorphisms

```agda
module _
  {l1 : Level} (X : Endo l1)
  where

  Component-Endo : UU (lsuc l1)
  Component-Endo = Σ (Endo l1) (mere-equiv-Endo X)

  endo-Component-Endo : Component-Endo → Endo l1
  endo-Component-Endo = pr1

  type-Component-Endo : Component-Endo → UU l1
  type-Component-Endo = pr1 ∘ endo-Component-Endo

  endomorphism-Component-Endo :
    (T : Component-Endo) → type-Component-Endo T → type-Component-Endo T
  endomorphism-Component-Endo T = pr2 (endo-Component-Endo T)

  mere-equiv-Component-Endo :
    (T : Component-Endo) → mere-equiv-Endo X (endo-Component-Endo T)
  mere-equiv-Component-Endo T = pr2 T

  canonical-Component-Endo : Component-Endo
  pr1 canonical-Component-Endo = X
  pr2 canonical-Component-Endo = refl-mere-equiv-Endo X
```

### Equivalences of types equipped with an endomorphism in a given component

```agda
module _
  {l1 : Level} (X : Endo l1)
  where

  equiv-Component-Endo : (T S : Component-Endo X) → UU l1
  equiv-Component-Endo T S =
    equiv-Endo (endo-Component-Endo X T) (endo-Component-Endo X S)

  id-equiv-Component-Endo : (T : Component-Endo X) → equiv-Component-Endo T T
  id-equiv-Component-Endo T = id-equiv-Endo (endo-Component-Endo X T)

  equiv-eq-Component-Endo :
    (T S : Component-Endo X) → Id T S → equiv-Component-Endo T S
  equiv-eq-Component-Endo T .T refl = id-equiv-Component-Endo T

  is-contr-total-equiv-Component-Endo :
    is-contr
      ( Σ ( Component-Endo X)
          ( λ T → equiv-Component-Endo (canonical-Component-Endo X) T))
  is-contr-total-equiv-Component-Endo =
    is-contr-total-Eq-subtype
      ( is-contr-total-equiv-Endo X)
      ( λ Y → is-prop-type-trunc-Prop)
      ( X)
      ( id-equiv-Endo X)
      ( refl-mere-equiv-Endo X)

  is-equiv-equiv-eq-Component-Endo :
    (T : Component-Endo X) →
    is-equiv (equiv-eq-Component-Endo (canonical-Component-Endo X) T)
  is-equiv-equiv-eq-Component-Endo =
    fundamental-theorem-id
      ( is-contr-total-equiv-Component-Endo)
      ( equiv-eq-Component-Endo (canonical-Component-Endo X))
```
