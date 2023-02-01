---
title: Wild groups
---

```agda
module structured-types.wild-groups where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.binary-equivalences using (is-binary-equiv)
open import foundation.universe-levels using (Level; UU; lsuc)

open import structured-types.pointed-types using
  ( Pointed-Type)
open import structured-types.wild-monoids using
  ( Wild-Monoid; type-Wild-Monoid; mul-Wild-Monoid; mul-Wild-Monoid')
```

```agda
is-wild-group-Wild-Monoid :
  {l : Level} (M : Wild-Monoid l) → UU l
is-wild-group-Wild-Monoid M = is-binary-equiv (mul-Wild-Monoid M)

Wild-Group : (l : Level) → UU (lsuc l)
Wild-Group l = Σ (Wild-Monoid l) is-wild-group-Wild-Monoid
```
