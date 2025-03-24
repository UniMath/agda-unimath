# Total partial functions

```agda
open import foundation.function-extensionality-axiom

module foundation.total-partial-functions
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.partial-functions
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

A [partial function](foundation.partial-functions.md) `f : A → B` is said to be
{{#concept "total" Disambiguation="partial function" Agda=is-total-partial-function}}
if the [partial element](foundation.partial-elements.md) `f a` of `B` is defined
for every `a : A`. The type of total partial functions from `A` to `B` is
[equivalent](foundation-core.equivalences.md) to the type of
[functions](foundation-core.function-types.md) from `A` to `B`.

## Definitions

### The predicate of being a total partial function

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : partial-function l3 A B)
  where

  is-total-prop-partial-function : Prop (l1 ⊔ l3)
  is-total-prop-partial-function =
    Π-Prop A (is-defined-prop-partial-function f)

  is-total-partial-function : UU (l1 ⊔ l3)
  is-total-partial-function = type-Prop is-total-prop-partial-function
```

### The type of total partial functions

```agda
total-partial-function :
  {l1 l2 : Level} (l3 : Level) → UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
total-partial-function l3 A B =
  Σ (partial-function l3 A B) is-total-partial-function
```
