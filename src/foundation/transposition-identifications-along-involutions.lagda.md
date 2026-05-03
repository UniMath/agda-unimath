# Transposing identifications along sections

```agda
module foundation.transposition-identifications-along-involutions where
```

<details><summary>Imports</summary>

```agda
open import foundation.involutions
open import foundation.universe-levels

open import foundation-core.identity-types
```

</details>

## Idea

If `f : A → A` is an [involution](foundation.involutions.md), then we have an
[equivalence](foundation-core.equivalences.md)

```text
  f x ＝ y ≃ x = f y
```

for every x y : A.

## Definitions

### Transposing identifications along involutions

```agda
module _
  {l1 : Level} {A : UU l1} {f : A → A} (H : is-involution f)
  where

  eq-transpose-involution :
    {x y : A} → x ＝ f y → f x ＝ y
  eq-transpose-involution refl = H _

  eq-transpose-involution' :
    {x y : A} → f x ＝ y → x ＝ f y
  eq-transpose-involution' refl = inv (H _)
```
