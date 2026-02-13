# Postfixpoints of endomaps on MacNeille real numbers

```agda
module real-numbers.postfixpoints-endomaps-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.universe-levels

open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.macneille-real-numbers
```

</details>

## Idea

For an endomap `g : ℝₘ → ℝₘ`, a
{{#concept "postfixpoint" Disambiguation="of an endomap on the MacNeille reals" Agda=is-postfixpoint-endomap-macneille-ℝ}}
is an element `x` such that `x ≤ g x`.

## Definitions

```agda
module _
  {l : Level}
  (g : macneille-ℝ l → macneille-ℝ l)
  (x : macneille-ℝ l)
  where

  is-postfixpoint-prop-endomap-macneille-ℝ : Prop l
  is-postfixpoint-prop-endomap-macneille-ℝ = leq-prop-macneille-ℝ x (g x)

  is-postfixpoint-endomap-macneille-ℝ : UU l
  is-postfixpoint-endomap-macneille-ℝ =
    type-Prop is-postfixpoint-prop-endomap-macneille-ℝ
```
