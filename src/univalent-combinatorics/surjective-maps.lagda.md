# Surjective maps between finite types

```agda
module univalent-combinatorics.surjective-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.surjective-maps public

open import foundation.decidable-types
open import foundation.universe-levels

open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.fibers-of-maps
open import univalent-combinatorics.finite-types
```

</details>

## Properties

```agda
is-decidable-is-surjective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-surjective f)
is-decidable-is-surjective-is-finite f HA HB =
  is-decidable-Π-is-finite HB
    ( λ y → is-decidable-type-trunc-Prop-is-finite (is-finite-fib f HA HB y))
```
