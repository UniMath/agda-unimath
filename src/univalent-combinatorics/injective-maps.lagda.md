# Injective maps between finite types

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module univalent-combinatorics.injective-maps
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where

open import foundation.injective-maps funext public
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types funext univalence truncations
open import foundation.identity-types funext
open import foundation.universe-levels

open import univalent-combinatorics.decidable-dependent-function-types funext univalence truncations
open import univalent-combinatorics.equality-finite-types funext univalence truncations
open import univalent-combinatorics.finite-types funext univalence truncations
```

</details>

## Idea

Injectiveness in the context of finite types enjoys further properties.

## Properties

```agda
is-decidable-is-injective-is-finite' :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable ((x y : A) → Id (f x) (f y) → Id x y)
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
