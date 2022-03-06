# Inequality on W-types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.inequality-W-types where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.elementhood-relation-W-types using
  ( _∈-𝕎_; irreflexive-∈-𝕎)
open import foundation.empty-types using (empty)
open import foundation.identity-types using (Id; refl)
open import foundation.negation using (¬)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.W-types using (𝕎; tree-𝕎)
```

## Idea

The elementhood relation on W-types induces a strict ordering.

## Definition

### Strict inequality on W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data _le-𝕎_ (x : 𝕎 A B) : 𝕎 A B → UU (l1 ⊔ l2) where
    le-∈-𝕎 : {y : 𝕎 A B} → x ∈-𝕎 y → x le-𝕎 y
    propagate-le-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x le-𝕎 y → x le-𝕎 z
```

### Inequality on W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data _leq-𝕎_ (x : 𝕎 A B) : 𝕎 A B → UU (l1 ⊔ l2) where
    refl-leq-𝕎 : x leq-𝕎 x
    propagate-leq-𝕎 : {y z : 𝕎 A B} → y ∈-𝕎 z → x leq-𝕎 y → x leq-𝕎 z
```

### Paths in W-types

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  data Path-𝕎 : 𝕎 A B → UU (l1 ⊔ l2) where
    root : (w : 𝕎 A B) → Path-𝕎 w
    cons : (a : A) (f : B a → 𝕎 A B) (b : B a) →
           Path-𝕎 (f b) → Path-𝕎 (tree-𝕎 a f)

  length-Path-𝕎 : (w : 𝕎 A B) → Path-𝕎 w → ℕ
  length-Path-𝕎 w (root .w) = zero-ℕ
  length-Path-𝕎 .(tree-𝕎 a f) (cons a f b p) = succ-ℕ (length-Path-𝕎 (f b) p)

```

## Properties

### The strict ordering on W-types is transitive

```agda
  transitive-le-𝕎 : {x y z : 𝕎 A B} → y le-𝕎 z → x le-𝕎 y → x le-𝕎 z
  transitive-le-𝕎 {x = x} {y} {z} (le-∈-𝕎 H) K =
    propagate-le-𝕎 H K
  transitive-le-𝕎 {x = x} {y} {z} (propagate-le-𝕎 L H) K =
    propagate-le-𝕎 L (transitive-le-𝕎 H K)
```

### The strict ordering on W-types is irreflexive

```agda
  irreflexive-le-𝕎 :
    {x : 𝕎 A B} → ¬ (x le-𝕎 x)
  irreflexive-le-𝕎 {x = x} (le-∈-𝕎 H) = irreflexive-∈-𝕎 x H
  irreflexive-le-𝕎 {x = tree-𝕎 x α} (propagate-le-𝕎 (pair b refl) H) =
    irreflexive-le-𝕎 {x = α b} (transitive-le-𝕎 H (le-∈-𝕎 (pair b refl)))
```

### The strict ordering on W-types is asymmetric

```agda
  asymmetric-le-𝕎 :
    {x y : 𝕎 A B} → x le-𝕎 y → y le-𝕎 x → empty
  asymmetric-le-𝕎 H K = irreflexive-le-𝕎 (transitive-le-𝕎 H K)
```
