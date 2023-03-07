# Hilbert's ε-operators

```agda
module foundation.hilberts-epsilon-operators where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.universe-levels
```

</details>

## Idea

Hilbert's ε-operator at a type `A` is a map `type-trunc-Prop A → A`. Contrary to Hilbert, we will not assume that such an operator exists for each type `A`.

## Definition

```agda
ε-operator-Hilbert : {l : Level} → UU l → UU l
ε-operator-Hilbert A = type-trunc-Prop A → A
```

## Properties

### The existence of Hilbert's ε-operators is invariant under equivalences

```agda
ε-operator-equiv :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  ε-operator-Hilbert X → ε-operator-Hilbert Y
ε-operator-equiv e f =
  (map-equiv e ∘ f) ∘ (map-trunc-Prop (map-inv-equiv e))

ε-operator-equiv' :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) →
  ε-operator-Hilbert Y → ε-operator-Hilbert X
ε-operator-equiv' e f =
  (map-inv-equiv e ∘ f) ∘ (map-trunc-Prop (map-equiv e))
```
