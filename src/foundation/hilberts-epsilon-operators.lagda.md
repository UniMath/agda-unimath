# Hilbert's ε-operators

```agda
module foundation.hilberts-epsilon-operators where
```

<details><summary>Imports</summary>

```agda
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

{{#concept "Hilbert's ε-operator" Disambiguation="on types" Agda=ε-operator-Hilbert}}
on a type `A` is a map

```text
  ε : ║A║₋₁ → A
```

Some authors also refer to this as _split support_ {{#cite KECA17}}. Contrary to
Hilbert, we will not assume that such an operator exists for each type `A`.

## Definition

```agda
ε-operator-Hilbert : {l : Level} → UU l → UU l
ε-operator-Hilbert A = type-trunc-Prop A → A
```

## Properties

### The existence of Hilbert's `ε`-operators is invariant under equivalences

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

## References

{{#bibliography}}

## See also

- [Global choice](foundation.global-choice.md)

## External links

- [Epsilon calculus](https://en.wikipedia.org/wiki/Epsilon_calculus) at
  Wikipedia
