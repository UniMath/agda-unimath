# Types equipped with endomorphisms

```agda
module structured-types.types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.endomorphisms
open import foundation.universe-levels
```

</details>

## Idea

A type equipped with an endomorphism consists of a type `A` equipped with a map `A → A`.

## Definitions

### Types equipped with endomorphisms

```agda
Endo : (l : Level) → UU (lsuc l)
Endo l = Σ (UU l) endo

module _
  {l : Level} (X : Endo l)
  where

  type-Endo : UU l
  type-Endo = pr1 X

  endomorphism-Endo : type-Endo → type-Endo
  endomorphism-Endo = pr2 X
```
