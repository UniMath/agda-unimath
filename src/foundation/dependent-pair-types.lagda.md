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

Consider a type family `B` over `A`. The
{{#concept "dependent pair type" Agda=Σ}} `Σ A B` is the type consisting of
{{#concept "(dependent) pairs" Agda=pair Agda=_,_}} `(a , b)` where `a : A` and
`b : B a`. Such pairs are sometimes called dependent pairs because the type of
`b` depends on the value of the first component `a`.

## Definitions

### The dependent pair type

```agda
record Σ {l1 l2 : Level} (A : UU l1) (B : A → UU l2) : UU (l1 ⊔ l2) where
  eta-equality
  constructor pair
  field
    pr1 : A
    pr2 : B pr1

open Σ public

{-# BUILTIN SIGMA Σ #-}
{-# INLINE pair #-}

infixr 3 _,_
pattern _,_ a b = pair a b
```

### The induction principle for dependent pair types

```agda
ind-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((x : A) (y : B x) → C (x , y)) → (t : Σ A B) → C t
ind-Σ f (x , y) = f x y
```

### The recursion principle for dependent pair types

```agda
rec-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : UU l3} →
  ((x : A) → B x → C) → Σ A B → C
rec-Σ = ind-Σ
```

### The evaluation function for dependent pairs

```agda
ev-pair :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  ((t : Σ A B) → C t) → (x : A) (y : B x) → C (x , y)
ev-pair f x y = f (x , y)
```

We show that `ev-pair` is the inverse to `ind-Σ` in
[`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).

### Iterated dependent pair constructors

```agda
triple :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  (a : A) (b : B a) → C a b → Σ A (λ x → Σ (B x) (C x))
triple a b c = (a , b , c)

triple' :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : Σ A B → UU l3} →
  (a : A) (b : B a) → C (pair a b) → Σ (Σ A B) C
triple' a b c = ((a , b) , c)
```

### Families on dependent pair types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  where

  fam-Σ : ((x : A) → B x → UU l3) → Σ A B → UU l3
  fam-Σ C (x , y) = C x y
```
