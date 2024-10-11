# Iterating dependent functions

```agda
module foundation.iterating-dependent-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.exponentiation-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.multiplicative-monoid-of-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-homotopies
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.iterating-functions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.endomorphisms
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sets

open import group-theory.monoid-actions
```

</details>

## Idea

Given a dependent map `g : (x : X) → C x → C (f x)` over a map `f : X → X` then
`g` can be
{{#concept "iterated" Disambiguation="dependent map of types" Agda=iterate-dependent}}
by repeatedly applying `g`.

## Definition

### Iterating dependent functions

```agda
module _
  {l1 l2 : Level} {X : UU l1} {C : X → UU l2} {f : X → X}
  where

  iterate-dependent :
    (k : ℕ) → ((x : X) → C x → C (f x)) → (x : X) → C x → C (iterate k f x)
  iterate-dependent zero-ℕ g x y = y
  iterate-dependent (succ-ℕ k) g x y =
    g (iterate k f x) (iterate-dependent k g x y)

  iterate-dependent' :
    (k : ℕ) → ((x : X) → C x → C (f x)) → (x : X) → C x → C (iterate' k f x)
  iterate-dependent' zero-ℕ g x y = y
  iterate-dependent' (succ-ℕ k) g x y = iterate-dependent' k g (f x) (g x y)
```

## Properties

### The two definitions of iterating dependent functions are homotopic

```agda
module _
  {l1 l2 : Level} {X : UU l1} {C : X → UU l2} {f : X → X}
  where

  reassociate-iterate-dependent-succ-ℕ :
    (k : ℕ) (g : (x : X) → C x → C (f x)) (x : X) (y : C x) →
    dependent-identification C
      ( reassociate-iterate-succ-ℕ k f x)
      ( g (iterate k f x) (iterate-dependent k g x y))
      ( iterate-dependent k g (f x) (g x y))
  reassociate-iterate-dependent-succ-ℕ zero-ℕ g x y = refl
  reassociate-iterate-dependent-succ-ℕ (succ-ℕ k) g x y =
    equational-reasoning
      tr C
        ( reassociate-iterate-succ-ℕ (succ-ℕ k) f x)
        ( g (iterate (succ-ℕ k) f x) (iterate-dependent (succ-ℕ k) g x y))
      ＝
      g ( iterate k f (f x))
        ( tr C
          ( reassociate-iterate-succ-ℕ k f x)
          ( g (iterate k f x) (iterate-dependent k g x y)))
      by
        tr-ap f g
          ( reassociate-iterate-succ-ℕ k f x)
          ( iterate-dependent (succ-ℕ k) g x y)
      ＝ g (iterate k f (f x)) (iterate-dependent k g (f x) (g x y))
      by
        ap
          ( g (iterate k f (f x)))
          ( reassociate-iterate-dependent-succ-ℕ k g x y)

  reassociate-iterate-dependent :
    (k : ℕ) (g : (x : X) → C x → C (f x)) (x : X) (y : C x) →
    dependent-identification C
      ( reassociate-iterate k f x)
      ( iterate-dependent k g x y)
      ( iterate-dependent' k g x y)
  reassociate-iterate-dependent zero-ℕ g x y = refl
  reassociate-iterate-dependent (succ-ℕ k) g x y =
    concat-dependent-identification C
      ( reassociate-iterate-succ-ℕ k f x)
      ( reassociate-iterate k f (f x))
      ( reassociate-iterate-dependent-succ-ℕ k g x y)
      ( reassociate-iterate-dependent k g (f x) (g x y))
```
