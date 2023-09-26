# Crisp types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.universe-levels
```

</details>

## Idea

We record here some basic facts about crisp types.

## Properties

```agda
crisp-ind-path :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {@♭ a : A} →
  (C : (@♭ y : A) (p : a ＝ y) → UU l2) →
  C a refl →
  (@♭ y : A) (@♭ p : a ＝ y) → C y p
crisp-ind-path C b _ refl = b
```
