# Identity types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation-core.identity-types where

open import foundation-core.universe-levels using (UU; Level)
```

## Idea

The equality relation on a type is a reflexive relation, with the universal property that it maps uniquely into any other reflexive relation. In type theory, we introduce the identity type as an inductive family of types, where the induction principle can be understood as expressing that the identity type is the least reflexive relation.

## Defnition

```agda
data Id {i : Level} {A : UU i} (x : A) : A → UU i where
  refl : Id x x

{-# BUILTIN EQUALITY Id  #-}
```

## Structure

### Concatenation of identifications

```agda
module _
  {l : Level} {A : UU l}
  where
  
  _∙_ : {x y z : A} → Id x y → Id y z → Id x z
  refl ∙ q = q

  concat : {x y : A} → Id x y → (z : A) → Id y z → Id x z
  concat p z q = p ∙ q

  concat' : (x : A) {y z : A} → Id y z → Id x y → Id x z
  concat' x q p = p ∙ q
```

### Inverting identifications

```agda
module _
  {l : Level} {A : UU l}
  where

  inv : {x y : A} → Id x y → Id y x
  inv refl = refl
```

### Functorial action of identity types

```agda
ap :
  {i j : Level} {A : UU i} {B : UU j} (f : A → B) {x y : A} (p : Id x y) →
  Id (f x) (f y)
ap f refl = refl
```
