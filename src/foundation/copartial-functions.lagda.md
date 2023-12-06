# Copartial functions

```agda
module foundation.copartial-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.copartial-elements
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "copartial function"}} from `A` to `B` is a map from `A` into the
type of [copartial elements](foundation.copartial-elements.md) of `B`. I.e., a
copartial function is a map

```text
  A → Σ (Q : Prop), A * Q
```

where `- * Q` is the
[closed modality](orthogonal-factorization-systems.closed-modalities.md).

A value of a copartial function `f` at `a : A` is said to be
{{#concept "prohibited" Disambiguation="copartial function"}} if the copartial
element `f a` of `B` is prohibited.

**Note:** The topic of copartial functions is not known in the literature, and
our formalization on this topic should be considered experimental.

## Definitions

### Copartial functions

```agda
copartial-function :
  {l1 l2 : Level} (l3 : Level) → UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
copartial-function l3 A B = A → copartial-element l3 B
```

### Prohibited values of copartial functions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : copartial-function l3 A B)
  (a : A)
  where

  is-prohibited-prop-copartial-function : Prop l3
  is-prohibited-prop-copartial-function =
    is-prohibited-prop-copartial-element (f a)

  is-prohibited-copartial-function : UU l3
  is-prohibited-copartial-function = is-prohibited-copartial-element (f a)
```

### Copartial functions obtained from functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  copartial-function-function : copartial-function lzero A B
  copartial-function-function a = unit-copartial-element (f a)
```
