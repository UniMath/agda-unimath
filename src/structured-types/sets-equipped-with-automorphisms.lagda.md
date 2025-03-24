# Sets equipped with automorphisms

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module structured-types.sets-equipped-with-automorphisms
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms funext univalence
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels
```

</details>

## Idea

A **set equipped with an automorphism** is a pair consisting of a
[set](foundation.sets.md) `A` and an [automorphism](foundation.automorphisms.md)
on `e : A ≃ A`.

## Definitions

### Sets equipped with automorphisms

```agda
Set-With-Automorphism : (l : Level) → UU (lsuc l)
Set-With-Automorphism l = Σ (Set l) (Aut ∘ type-Set)

module _
  {l : Level} (A : Set-With-Automorphism l)
  where

  set-Set-With-Automorphism : Set l
  set-Set-With-Automorphism = pr1 A

  type-Set-With-Automorphism : UU l
  type-Set-With-Automorphism = type-Set set-Set-With-Automorphism

  is-set-type-Set-With-Automorphism : is-set type-Set-With-Automorphism
  is-set-type-Set-With-Automorphism = is-set-type-Set set-Set-With-Automorphism

  aut-Set-With-Automorphism : Aut type-Set-With-Automorphism
  aut-Set-With-Automorphism = pr2 A

  map-Set-With-Automorphism :
    type-Set-With-Automorphism → type-Set-With-Automorphism
  map-Set-With-Automorphism = map-equiv aut-Set-With-Automorphism
```
