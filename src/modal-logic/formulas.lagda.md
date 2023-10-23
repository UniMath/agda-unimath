# Modal logic formulas

```agda
module modal-logic.formulas where
```

<details><summary>Imports</summary>

```agda
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l : Level} (i : Set l)
  where

  infixr 6 _⇒_
  infixr 25 □_

  data formula : UU l where
    var : type-Set i → formula
    ⊥ : formula
    _⇒_ : formula → formula → formula
    □_ : formula → formula

module _
  {l : Level} {i : Set l}
  where

  infixr 25 ~_
  infixr 25 ~~_
  infixl 10 _∨_
  infixl 15 _∧_
  infixr 25 ◇_

  ~_ : formula i → formula i
  ~ a = a ⇒ ⊥

  ~~_ : formula i → formula i
  ~~ a = ~ ~ a

  _∨_ : formula i → formula i → formula i
  a ∨ b = ~ a ⇒ b

  _∧_ : formula i → formula i → formula i
  a ∧ b = ~ (a ⇒ ~ b)

  ⊤ : formula i
  ⊤ = ~ ⊥

  ◇_ : formula i → formula i
  ◇ a = ~ □ ~ a
```
