# Large subtypes

```agda
module foundation.large-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "large subtype"}} of a universe polymorphic type
`X : (l : Level) → UU (α l)` is a [subtype](foundation.subtypes.md) of `X l` at
each universe level `l`.

## Definition

```agda
large-subtype :
  {α : Level → Level} → (Level → Level) → ((l : Level) → UU (α l)) → UUω
large-subtype β X = (l : Level) → subtype (β l) (X l)

type-large-subtype :
  {α β : Level → Level} {X : (l : Level) → UU (α l)} →
  large-subtype β X → (l : Level) → UU (α l ⊔ β l)
type-large-subtype S l = type-subtype (S l)

is-in-large-subtype :
  {α β : Level → Level} {X : (l : Level) → UU (α l)} {l : Level} →
  large-subtype β X → X l → UU (β l)
is-in-large-subtype {l = l} S = is-in-subtype (S l)

prop-is-in-large-subtype :
  {α β : Level → Level} {X : (l : Level) → UU (α l)} {l : Level} →
  large-subtype β X → X l → Prop (β l)
prop-is-in-large-subtype {l = l} S = S l

inclusion-large-subtype :
  {α β : Level → Level} {X : (l : Level) → UU (α l)} (S : large-subtype β X) →
  {l : Level} → type-large-subtype S l → X l
inclusion-large-subtype S = pr1
```

## Properties

### Equality on large subtypes

```agda
eq-type-large-subtype :
  {α β : Level → Level} {X : (l : Level) → UU (α l)} (S : large-subtype β X) →
  {l : Level} {x y : type-large-subtype S l} → pr1 x ＝ pr1 y → x ＝ y
eq-type-large-subtype S {l} = eq-type-subtype (S l)
```
