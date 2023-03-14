# Fibers of pointed maps

```agda
module structured-types.fibers-of-pointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.universe-levels

open import structured-types.pointed-maps
open import structured-types.pointed-types
```

</details>

## Definition

```agda
fib-Pointed-Type :
  {l1 l2 : Level} (A : Pointed-Type l1) (B : Pointed-Type l2) →
  (A →* B) → Pointed-Type (l1 ⊔ l2)
pr1 (fib-Pointed-Type A B f) = fib (map-pointed-map A B f) (pt-Pointed-Type B)
pr1 (pr2 (fib-Pointed-Type A B f)) = pt-Pointed-Type A
pr2 (pr2 (fib-Pointed-Type A B f)) = preserves-point-pointed-map A B f
```
