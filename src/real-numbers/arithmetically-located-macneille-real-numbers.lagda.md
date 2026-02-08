# Arithmetically located MacNeille real numbers

```agda
module real-numbers.arithmetically-located-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import real-numbers.macneille-real-numbers
open import real-numbers.arithmetically-located-dedekind-cuts
```

</details>

## Definition

A [MacNeille real number](real-numbers.macneille-real-numbers.md) is
{{#concept "arithmetically located" Disambiguation="MacNeille real number" Agda=is-arithmetically-located-macneille-ℝ}}
if its underlying Dedekind cuts form an
[arithmetically located pair of Dedekind cuts](real-numbers.arithmetically-located-dedekind-cuts.md).

## Definition

```agda
module _
  {l : Level} (x : macneille-ℝ l)
  where

  is-arithmetically-located-macneille-ℝ : UU l
  is-arithmetically-located-macneille-ℝ =
    is-arithmetically-located-lower-upper-ℝ
      ( lower-real-macneille-ℝ x)
      ( upper-real-macneille-ℝ x)
```
