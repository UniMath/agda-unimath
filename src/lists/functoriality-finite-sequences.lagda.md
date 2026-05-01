# Functoriality of the type of finite sequences

```agda
module lists.functoriality-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import lists.finite-sequences

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Any map `f : A → B` determines a map between
[finite sequences](lists.finite-sequences.md)
`fin-sequence A n → fin-sequence B n` for every `n`. This is the
{{#concept "functorial action" Disambiguation="of finite sequences" Agda=map-fin-sequence}}
of finite sequences.

## Definition

### Functoriality of the type of finite sequences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-fin-sequence :
    (n : ℕ) → (A → B) → fin-sequence A n → fin-sequence B n
  map-fin-sequence n f v = f ∘ v

  htpy-fin-sequence :
    (n : ℕ) {f g : A → B} → (f ~ g) →
    map-fin-sequence n f ~ map-fin-sequence n g
  htpy-fin-sequence n = htpy-postcomp (Fin n)
```

### Binary functoriality of the type of finite sequences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  binary-map-fin-sequence :
    (n : ℕ) → (A → B → C) →
    fin-sequence A n → fin-sequence B n → fin-sequence C n
  binary-map-fin-sequence n f v w i = f (v i) (w i)
```
