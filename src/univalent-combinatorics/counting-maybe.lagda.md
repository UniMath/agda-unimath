# Counting the elements in Maybe

```agda
open import foundation.function-extensionality-axiom

module
  univalent-combinatorics.counting-maybe
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences-maybe funext
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.maybe

open import univalent-combinatorics.coproduct-types funext
open import univalent-combinatorics.counting funext
```

</details>

## Idea

The elements of a type `X` can be counted if and only if the elements of
`Maybe X` can be counted.

```agda
count-Maybe : {l : Level} {X : UU l} → count X → count (Maybe X)
count-Maybe {l} {X} e = count-coproduct e count-unit

abstract
  is-nonzero-number-of-elements-count-Maybe :
    {l : Level} {X : UU l} (e : count (Maybe X)) →
    is-nonzero-ℕ (number-of-elements-count e)
  is-nonzero-number-of-elements-count-Maybe e p =
    is-empty-is-zero-number-of-elements-count e p exception-Maybe

is-successor-number-of-elements-count-Maybe :
  {l : Level} {X : UU l} (e : count (Maybe X)) →
  is-successor-ℕ (number-of-elements-count e)
is-successor-number-of-elements-count-Maybe e =
  is-successor-is-nonzero-ℕ (is-nonzero-number-of-elements-count-Maybe e)

count-count-Maybe :
  {l : Level} {X : UU l} → count (Maybe X) → count X
count-count-Maybe (pair k e) with
  is-successor-number-of-elements-count-Maybe (pair k e)
... | pair l refl = pair l (equiv-equiv-Maybe e)
```
