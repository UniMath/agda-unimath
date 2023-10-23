# Modal logic K syntax

```agda
module modal-logic.K-syntax where
```

<details><summary>Imports</summary>

```agda
open import foundation.sets
open import foundation.universe-levels

open import modal-logic.formulas
```

</details>

## Idea

TODO

## Definition

```agda
infix 5 ⊢_

data ⊢_ {l : Level} {i : Set l} : formula i → UU l where
  ax-k : (a b : formula i) → ⊢ a ⇒ b ⇒ a
  ax-s : (a b c : formula i) → ⊢ (a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ (a ⇒ c)
  ax-dn : (a : formula i) → ⊢ ~~ a ⇒ a
  ax-n : (a b : formula i) → ⊢ □ (a ⇒ b) ⇒ □ a ⇒ □ b
  mp : {a b : formula i} → ⊢ a ⇒ b → ⊢ a → ⊢ b
  nec : {a : formula i} → ⊢ a → ⊢ □ a
```
