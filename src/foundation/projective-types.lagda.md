---
title: Projective types
---

```agda
module foundation.projective-types where

open import foundation.functions
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universe-levels
```

## Idea

A type `X` is said to be **projective** if for every surjective map `f : A → B` into a set `B` the postcomposition function

```md
  (X → A) → (X → B)
```

is surjective. This is equivalent to the condition that for every equivalence relation `R` on a type `A` the natural map

```md
  (X → A)/~ → (X → A/R)
```

is an equivalence. The latter map is always an embedding, and it is an equivalence for every `X`, `A`, and `R` if and only if the axiom of choice holds.

## Definition

```agda
is-projective :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
is-projective l2 l3 X =
  (A : UU l2) (B : Set l3) (f : A → type-Set B) → is-surjective (postcomp X f)
```

## See also

- The natural map `(X → A)/~ → (X → A/R)` was studied in [foundation.exponents-set-quotients](foundation.exponents-set-quotients.html)
