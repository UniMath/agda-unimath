# Types equipped with endomorphisms

```agda
module structured-types.types-equipped-with-endomorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.endomorphisms
open import foundation.function-types
open import foundation.unit-type
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "type equipped with an endomorphism" Agda=Type-With-Endomorphism}}
consists of a type `A` [equipped](foundation.structure.md) with a map `A → A`.

## Definitions

### Types equipped with endomorphisms

```agda
Type-With-Endomorphism : (l : Level) → UU (lsuc l)
Type-With-Endomorphism l = Σ (UU l) endo

module _
  {l : Level} (X : Type-With-Endomorphism l)
  where

  type-Type-With-Endomorphism : UU l
  type-Type-With-Endomorphism = pr1 X

  endomorphism-Type-With-Endomorphism :
    type-Type-With-Endomorphism → type-Type-With-Endomorphism
  endomorphism-Type-With-Endomorphism = pr2 X
```

## Example

### Unit type equipped with endomorphisms

```agda
trivial-Type-With-Endomorphism : {l : Level} → Type-With-Endomorphism l
pr1 (trivial-Type-With-Endomorphism {l}) = raise-unit l
pr2 trivial-Type-With-Endomorphism = id
```
