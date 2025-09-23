# Functoriality of disjunction

```agda
module foundation.functoriality-disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.disjunction
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-propositional-truncation
open import foundation.universe-levels
```

</details>

## Idea

Any two implications `f : A ⇒ B` and `g : C ⇒ D` induce an implication
`map-disjunction f g : (A ∨ B) ⇒ (C ∨ D)`.

## Definitions

### The functorial action of disjunction

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D)
  where

  map-disjunction : disjunction-type A C → disjunction-type B D
  map-disjunction = map-trunc-Prop (map-coproduct f g)
```
