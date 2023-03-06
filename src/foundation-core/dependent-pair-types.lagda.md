# Dependent pair types

```agda
{-# OPTIONS --safe #-}
```

<details><summary>Imports</summary>
```agda
module foundation-core.dependent-pair-types where
open import foundation-core.universe-levels
```
</details>

## Idea

When `B` is a family of types over `A`, then we can form the type of pairs `pair a b` consisting of an element `a : A` and an element `b : B a`. Such pairs are called dependent pairs, since the type of the second component depends on the first component.

## Definition

```agda
record Σ {l1 l2} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1

open Σ public

{-# BUILTIN SIGMA Σ #-}

infixr 10 _,_
pattern _,_ a  b = pair a b
```

## Constructions

```agda
ind-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : A) (y : B x) → C (pair x y)) → ((t : Σ A B) → C t)
ind-Σ f (pair x y) = f x y

ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (pair x y)
ev-pair f x y = f (pair x y)

triple :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  (a : A) (b : B a) → C a b → Σ A (λ x → Σ (B x) (C x))
pr1 (triple a b c) = a
pr1 (pr2 (triple a b c)) = b
pr2 (pr2 (triple a b c)) = c

triple' :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  (a : A) (b : B a) → C (pair a b) → Σ (Σ A B) C
pr1 (pr1 (triple' a b c)) = a
pr2 (pr1 (triple' a b c)) = b
pr2 (triple' a b c) = c
```

### Families on dependent pair types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  fam-Σ : ((x : A) → B x → UU l3) → Σ A B → UU l3
  fam-Σ C (pair x y) = C x y
```
