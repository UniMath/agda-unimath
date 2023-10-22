# Global choice

```agda
module foundation.global-choice where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.functoriality-propositional-truncation
open import foundation.hilberts-epsilon-operators
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.negation

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Global choice is the principle that there is a map from `type-trunc-Prop A` back
into `A`, for any type `A`. Here, we say that a type `A` satisfies global choice
if there is such a map.

## Definition

### The global choice principle

```agda
Global-Choice : (l : Level) → UU (lsuc l)
Global-Choice l = (A : UU l) → ε-operator-Hilbert A
```

## Properties

### The global choice principle is inconsistent in `agda-unimath`

```agda
abstract
  no-global-choice :
    {l : Level} → ¬ (Global-Choice l)
  no-global-choice f =
    no-section-type-2-Element-Type
      ( λ X →
        f (pr1 X) (map-trunc-Prop (λ e → map-equiv e (zero-Fin 1)) (pr2 X)))
```
