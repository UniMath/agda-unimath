# Diagonal span diagrams

```agda
open import foundation.function-extensionality-axiom

module foundation.diagonal-span-diagrams
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.span-diagrams funext
open import foundation.universe-levels
```

</details>

## Idea

Consider a map `f : A → B`. The
{{#concept "diagonal span diagram" Agda=diagonal-span-diagram}} of `f` is the
[span diagram](foundation.span-diagrams.md)

```text
       f       f
  B <----- A -----> B.
```

## Definitions

### Diagonal span diagrams of maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  diagonal-span-diagram : span-diagram l2 l2 l1
  diagonal-span-diagram = make-span-diagram f f
```
