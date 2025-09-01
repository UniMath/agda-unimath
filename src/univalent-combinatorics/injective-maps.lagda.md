# Injective maps between finite types

```agda
module univalent-combinatorics.injective-maps where

open import foundation.injective-maps public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.decidable-dependent-function-types
open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Injectiveness in the context of finite types enjoys further properties.

## Properties

```agda
is-decidable-is-injective-is-finite' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable ((x y : A) → f x ＝ f y → x ＝ y)
is-decidable-is-injective-is-finite' f HA HB =
  is-decidable-Π-is-finite HA
    ( λ x →
      is-decidable-Π-is-finite HA
        ( λ y →
          is-decidable-function-type
            ( has-decidable-equality-is-finite HB (f x) (f y))
            ( has-decidable-equality-is-finite HA x y)))

is-decidable-is-injective-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-injective f)
is-decidable-is-injective-is-finite f HA HB =
  is-decidable-iff
    ( λ p {x} {y} → p x y)
    ( λ p x y → p)
    ( is-decidable-is-injective-is-finite' f HA HB)
```
