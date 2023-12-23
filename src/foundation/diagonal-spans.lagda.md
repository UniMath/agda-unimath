# Diagonal spans

```agda
module foundation.diagonal-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

Consider a map `f : A → B`. The {{#concept "diagonal span"}} of `f` is the [span](foundation.spans.md)

```text
       f       f
  B <----- A -----> B.
```

## Definitions

### Diagonal spans of maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  diagonal-span : span l2 l2 l1
  diagonal-span = make-span f f
```
