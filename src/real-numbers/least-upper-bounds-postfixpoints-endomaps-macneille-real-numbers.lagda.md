# Least upper bounds of postfixpoints of MacNeille-real endomaps

```agda
module real-numbers.least-upper-bounds-postfixpoints-endomaps-macneille-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.least-upper-bounds-postfixpoints-endomaps-posets

open import real-numbers.inequality-macneille-real-numbers
open import real-numbers.macneille-real-numbers
```

</details>

## Idea

For an endomap `g : ℝₘ → ℝₘ`, we consider the family of all its postfixpoints. A
least upper bound of this family is a candidate greatest postfixpoint.

## Definitions

```agda
indexing-type-postfixpoints-endomap-macneille-ℝ :
  {l : Level} (g : macneille-ℝ l → macneille-ℝ l) → UU (lsuc l)
indexing-type-postfixpoints-endomap-macneille-ℝ {l} g =
  indexing-type-postfixpoints-endomap-Poset
    ( poset-macneille-ℝ l)
    ( g)

family-of-elements-postfixpoints-endomap-macneille-ℝ :
  {l : Level} (g : macneille-ℝ l → macneille-ℝ l) →
  indexing-type-postfixpoints-endomap-macneille-ℝ g →
  macneille-ℝ l
family-of-elements-postfixpoints-endomap-macneille-ℝ {l} g =
  family-of-elements-postfixpoints-endomap-Poset
    ( poset-macneille-ℝ l)
    ( g)

is-least-upper-bound-postfixpoints-endomap-macneille-ℝ :
  {l : Level} (g : macneille-ℝ l → macneille-ℝ l) →
  macneille-ℝ l → UU (lsuc l)
is-least-upper-bound-postfixpoints-endomap-macneille-ℝ {l} g =
  is-least-upper-bound-postfixpoints-endomap-Poset
    ( poset-macneille-ℝ l)
    ( g)
```
