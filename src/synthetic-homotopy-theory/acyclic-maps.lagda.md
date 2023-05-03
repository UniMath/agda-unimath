# Acyclic maps

```agda
module synthetic-homotopy-theory.acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.fibers-of-maps
open import foundation.propositions
open import foundation.universe-levels

open import synthetic-homotopy-theory.acyclic-types
```

</details>

## Idea

A map `f : A → B` is said to be **acyclic** if its fibers are acyclic types.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-acyclic-map-Prop f = Π-Prop B (λ b → is-acyclic-Prop (fib f b))

  is-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-acyclic-map f = type-Prop (is-acyclic-map-Prop f)

  is-prop-is-acyclic-map : (f : A → B) → is-prop (is-acyclic-map f)
  is-prop-is-acyclic-map f = is-prop-type-Prop (is-acyclic-map-Prop f)
```
