# Types equipped with endomorphisms

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.types-equipped-with-endomorphisms
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.raising-universe-levels-unit-type
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.endomorphisms funext univalence
open import foundation-core.function-types
```

</details>

## Idea

A type equipped with an endomorphism consists of a type `A` equipped with a map
`A → A`.

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
