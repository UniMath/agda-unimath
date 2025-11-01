# The parametricity axiom

```agda
module foundation.parametricity-axiom where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.evaluation-functions
open import foundation.function-extensionality
open import foundation.mere-equality
open import foundation.parametric-types
open import foundation.reflecting-maps-equivalence-relations
open import foundation.retracts-of-types
open import foundation.sets
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-equivalences
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.type-theoretic-principle-of-choice

open import orthogonal-factorization-systems.null-types
```

</details>

## Idea

The {{#concept "parametricity axiom" Agda=Parametricity-Axiom}} states that all
types are [parametric](foundation.parametric-types.md). I.e., for each type
`X : 𝒰`, the [constant map](foundation.constant-maps.md)

```text
  X → (𝒰 → X)
```

is an [equivalence](foundation-core.equivalences.md).

## Definition

```agda
level-Parametricity-Axiom : (l : Level) → UU (lsuc l)
level-Parametricity-Axiom l = {X : UU l} → is-parametric l X

Parametricity-Axiom : UUω
Parametricity-Axiom = {l : Level} → level-Parametricity-Axiom l
```

## References

{{#bibliography}} {{#reference Lord25}}
