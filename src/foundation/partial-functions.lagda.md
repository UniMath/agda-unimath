# Partial functions

```agda
module foundation.partial-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.partial-elements
open import foundation.universe-levels

open import foundation-core.propositions
```

</details>

## Idea

A {{#concept "partial function" Agda=partial-function}} from `A` to `B` is a
function from `A` into the type of
[partial elements](foundation.partial-elements.md) of `B`. In other words, a
partial function is a function

```text
  A → Σ (P : Prop), (P → B).
```

Given a partial function `f : A → B` and an element `a : A`, we say that `f` is
{{#concept "defined" Disambiguation="partial function" Agda=is-defined-partial-function}}
at `a` if the partial element `f a` of `A` is defined.

Partial functions can be described
[equivalently](foundation-core.equivalences.md) as
[morphisms of arrows](foundation.morphisms-arrows.md)

```text
  ∅     1   ∅
  |     |   |
  |  ⇒  | ∘ |
  ∨     ∨   ∨
  A   Prop  B
```

where the composition operation is
[composition](species.composition-cauchy-series-species-of-types.md) of
[polynomial endofunctors](trees.polynomial-endofunctors.md).

## Definitions

### Partial dependent functions

```agda
partial-dependent-function :
  {l1 l2 : Level} (l3 : Level) (A : UU l1) (B : A → UU l2) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
partial-dependent-function l3 A B =
  (x : A) → partial-element l3 (B x)
```

### Partial functions

```agda
partial-function :
  {l1 l2 : Level} (l3 : Level) → UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
partial-function l3 A B = partial-dependent-function l3 A (λ _ → B)
```

### The predicate on partial dependent functions of being defined at an element in the domain

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (f : partial-dependent-function l3 A B) (a : A)
  where

  is-defined-prop-partial-dependent-function : Prop l3
  is-defined-prop-partial-dependent-function =
    is-defined-prop-partial-element (f a)

  is-defined-partial-dependent-function : UU l3
  is-defined-partial-dependent-function =
    type-Prop is-defined-prop-partial-dependent-function
```

### The predicate on partial functions of being defined at an element in the domain

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : partial-function l3 A B)
  (a : A)
  where

  is-defined-prop-partial-function : Prop l3
  is-defined-prop-partial-function =
    is-defined-prop-partial-dependent-function f a

  is-defined-partial-function : UU l3
  is-defined-partial-function =
    is-defined-partial-dependent-function f a
```

### The partial dependent function obtained from a dependent function

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x)
  where

  partial-dependent-function-dependent-function :
    partial-dependent-function lzero A B
  partial-dependent-function-dependent-function a =
    unit-partial-element (f a)
```

### The partial function obtained from a function

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  partial-function-function : partial-function lzero A B
  partial-function-function = partial-dependent-function-dependent-function f
```

## See also

- [Copartial functions](foundation.copartial-functions.md)
- [Partial elements](foundation.partial-elements.md)
- [Partial sequences](lists.partial-sequences.md)
