# The replacement axiom for type theory

```agda
module foundation.replacement where
```

<details><summary>Imports</summary>

```agda
open import foundation.images
open import foundation.locally-small-types

open import foundation-core.small-types
open import foundation-core.universe-levels
```

</details>

## Idea

The **type theoretic replacement axiom** asserts that the image of a map
`f : A → B` from a small type `A` into a locally small type `B` is small.

## Statement

```agda
Replacement : (l : Level) → UUω
Replacement l =
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-small l A → is-locally-small l B → is-small l (im f)
```

## Postulate

```agda
postulate replacement : {l : Level} → Replacement l
```

```agda
replacement-UU :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-locally-small l1 B → is-small l1 (im f)
replacement-UU f = replacement f is-small'
```
