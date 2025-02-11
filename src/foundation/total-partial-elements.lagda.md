# Total partial elements

```agda
module foundation.total-partial-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.partial-elements
open import foundation.universe-levels
```

</details>

## Idea

A [partial element](foundation.partial-elements.md) `a` of `A` is said to be
{{#concept "total" Disambiguation="partial element" Agda=total-partial-element}}
if it is defined. The type of total partial elements of `A` is
[equivalent](foundation-core.equivalences.md) to the type `A`.

## Definitions

### The type of total partial elements

```agda
total-partial-element :
  {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
total-partial-element l2 A =
  Σ (partial-element l2 A) is-defined-partial-element
```
