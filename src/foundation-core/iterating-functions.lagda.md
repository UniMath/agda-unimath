# Iterating functions

```agda
module foundation-core.iterating-functions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Any map `f : X → X` can be
{{#concept "iterated" Disambiguation="endo map of types" Agda=iterate Agda=iterate'}}
by repeatedly applying `f`.

## Definition

### Iterating functions

```agda
module _
  {l : Level} {X : UU l}
  where

  iterate : ℕ → (X → X) → (X → X)
  iterate zero-ℕ f x = x
  iterate (succ-ℕ k) f x = f (iterate k f x)

  iterate' : ℕ → (X → X) → (X → X)
  iterate' zero-ℕ f x = x
  iterate' (succ-ℕ k) f x = iterate' k f (f x)
```

### Homotopies of iterating functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (s : A → A) (t : B → B)
  where

  coherence-square-iterate :
    {f : A → B} (H : coherence-square-maps f s t f) →
    (n : ℕ) → coherence-square-maps f (iterate n s) (iterate n t) f
  coherence-square-iterate {f} H zero-ℕ x = refl
  coherence-square-iterate {f} H (succ-ℕ n) =
    pasting-vertical-coherence-square-maps
      ( f)
      ( iterate n s)
      ( iterate n t)
      ( f)
      ( s)
      ( t)
      ( f)
      ( coherence-square-iterate H n)
      ( H)
```

## Properties

### The two definitions of iterating are homotopic

```agda
module _
  {l : Level} {X : UU l}
  where

  reassociate-iterate-succ-ℕ :
    (k : ℕ) (f : X → X) (x : X) → iterate (succ-ℕ k) f x ＝ iterate k f (f x)
  reassociate-iterate-succ-ℕ zero-ℕ f x = refl
  reassociate-iterate-succ-ℕ (succ-ℕ k) f x =
    ap f (reassociate-iterate-succ-ℕ k f x)

  reassociate-iterate : (k : ℕ) (f : X → X) → iterate k f ~ iterate' k f
  reassociate-iterate zero-ℕ f x = refl
  reassociate-iterate (succ-ℕ k) f x =
    reassociate-iterate-succ-ℕ k f x ∙ reassociate-iterate k f (f x)
```
