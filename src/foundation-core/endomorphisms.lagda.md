---
title: Endomorphisms
---

```agda
module foundation-core.endomorphisms where

open import foundation.dependent-pair-types
open import foundation.functions
open import foundation.sets
open import foundation.universe-levels

open import structured-types.pointed-types
```

## Idea

An endomorphism on a type `A` is a map `A → A`.

## Definitions

### Endomorphisms

```agda
endo : {l : Level} → UU l → UU l
endo A = A → A

is-set-endo : {l : Level} {A : UU l} → is-set A → is-set (endo A)
is-set-endo H = is-set-function-type H

endo-Set : {l : Level} → UU-Set l → UU-Set l
pr1 (endo-Set A) = endo (type-Set A)
pr2 (endo-Set A) = is-set-endo (is-set-type-Set A)

endo-Pointed-Type : {l : Level} → UU l → Pointed-Type l
pr1 (endo-Pointed-Type X) = X → X
pr2 (endo-Pointed-Type X) = id
```
