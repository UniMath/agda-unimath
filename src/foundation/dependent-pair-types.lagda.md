# Dependent pair types

```agda
module foundation.dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

Consider a type family `B` over `A`. The **dependent pair type** `Σ A B` is the
type consisting of **(dependent) pairs** `(a , b)` where `a : A` and `b : B a`.
Such pairs are sometimes called dependent pairs because the type of `b` depends
on the value of the first component `a`.

## Definition

```agda
record Σ {l1 l2 : Level} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  constructor pair
  field
    pr1 : A
    pr2 : B pr1

open Σ public

{-# BUILTIN SIGMA Σ #-}

infixr 10 _,_
pattern _,_ a b = pair a b
```

## Constructions

```agda
ind-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : A) (y : B x) → C (pair x y)) → ((t : Σ A B) → C t)
ind-Σ f (x , y) = f x y

ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (pair x y)
ev-pair f x y = f (x , y)

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
  fam-Σ C (x , y) = C x y
```
