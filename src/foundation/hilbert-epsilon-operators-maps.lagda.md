# Hilbert ε-operators on maps

```agda
module foundation.hilbert-epsilon-operators-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.hilberts-epsilon-operators
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
```

</details>

## Idea

A
{{#concept "Hilbert ε-operator" Disambiguation="on a map" Agda=ε-operator-map}}
on a map $f : A → B$ is a family of
[Hilbert ε-operators](foundation.hilberts-epsilon-operators.md) on its
[fibers](foundation-core.fibers-of-maps.md). I.e., for every `y : B` there is an
operator

```text
  ε_y : ║ fiber f y ║₋₁ → fiber f y.
```

Some authors also refer to this as _split support_ {{#cite KECA17}}. Contrary to
Hilbert, we do not assume that such an operator exists for every map.

## Definitions

### The structure of a Hilbert ε-operator on a map

```agda
ε-operator-map :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
ε-operator-map {B = B} f = (y : B) → ε-operator-Hilbert (fiber f y)
```
