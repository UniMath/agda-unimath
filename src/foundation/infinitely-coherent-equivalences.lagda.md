# Infinitely coherent equivalences

```agda
{-# OPTIONS --guardedness --lossy-unification #-}

module foundation.infinitely-coherent-equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels
```

## Idea

A {{#concept "infinitely coherent equivalence"}} `e : A ≃ᶜ B` from `A` to `B`
consists of maps

```text
  f : A → B
  g : B → A
```

and for each `x : A` and `y : B` a infinitely coherent equivalence

```text
  transpose-eq : (f x ＝ y) ≃ᶜ (g y ＝ x).
```

Since this definition is infinite, it follows that for any `x : A` and `y : B` we have maps

```text
  f' : (f x ＝ y) → (g y ＝ x)
  g' : (g y ＝ x) → (f x ＝ y)
```

and for each `p : f x ＝ y` and `q : g y ＝ x` a infinitely coherent equivalence

```text
  transpose-eq : (f' p ＝ q) ≃ᶜ (g' q ＝ p).
```

In particular, we have identifications

```text
  f' x (f x) refl : g (f x) ＝ x
  g' y (g y) refl : f (g y) ＝ y,
```

which are the usual homotopies witnessing that `g` is a retraction and a section of `f`. By infinitely imposing the structure of a coherent equivalence, we have stated an infinite hierarchy of coherence conditions. In other words, the infinite condition on infinitely coherent equivalences is a way of stating infinite coherence for equivalences.

## Definitions

### The predicate of being a infinitely coherent equivalence

```agda
record is-infinitely-coherent-equivalence
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    map-inv-is-infinitely-coherent-equivalence : B → A
    map-transpose-is-infinitely-coherent-equivalence :
      (x : A) (y : B) →
      (f x ＝ y) → (x ＝ map-inv-is-infinitely-coherent-equivalence y)
    is-equiv-map-transpose-is-infinitely-coherent-equivalence :
      (x : A) (y : B) →
      is-infinitely-coherent-equivalence
        ( map-transpose-is-infinitely-coherent-equivalence x y)

open is-infinitely-coherent-equivalence public
```

### Infinitely coherent equivalences

```agda
record
  infinitely-coherent-equivalence
    {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    map : A → B
    map-inv : B → A
    eq :
      (x : A) (y : B) →
      infinitely-coherent-equivalence (map x ＝ y) (map-inv y ＝ x)

open infinitely-coherent-equivalence public

module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  infix 6 _≃ʰ_

  _≃ʰ_ : UU (l1 ⊔ l2)
  _≃ʰ_ = infinitely-coherent-equivalence A B
```

### Composition of infinitely coherent equivalences

```agda
is-infinitely-coherent-equivalence-comp :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {g : B → C} {f : A → B}
  (G : is-infinitely-coherent-equivalence g)
  (F : is-infinitely-coherent-equivalence f) →
  is-infinitely-coherent-equivalence (g ∘ f)
map-inv-is-infinitely-coherent-equivalence
  (is-infinitely-coherent-equivalence-comp G F) =
  map-inv-is-infinitely-coherent-equivalence F ∘
  map-inv-is-infinitely-coherent-equivalence G
map-transpose-is-infinitely-coherent-equivalence
  ( is-infinitely-coherent-equivalence-comp G F) x z p =
  map-transpose-is-infinitely-coherent-equivalence F x _
    ( map-transpose-is-infinitely-coherent-equivalence G _ z p)
is-equiv-map-transpose-is-infinitely-coherent-equivalence
  ( is-infinitely-coherent-equivalence-comp G F) x z =
  is-infinitely-coherent-equivalence-comp
    ( is-equiv-map-transpose-is-infinitely-coherent-equivalence F x _)
    ( is-equiv-map-transpose-is-infinitely-coherent-equivalence G _ z)
```

### Infinitely coherent equivalences obtained from equivalences

```agda
is-infinitely-coherent-equivalence-is-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} →
  is-equiv f → is-infinitely-coherent-equivalence f
map-inv-is-infinitely-coherent-equivalence
  ( is-infinitely-coherent-equivalence-is-equiv H) =
  map-inv-is-equiv H
map-transpose-is-infinitely-coherent-equivalence
  ( is-infinitely-coherent-equivalence-is-equiv H) x y =
  map-eq-transpose-equiv (_ , H)
is-equiv-map-transpose-is-infinitely-coherent-equivalence
  ( is-infinitely-coherent-equivalence-is-equiv H) x y =
  is-infinitely-coherent-equivalence-is-equiv
    ( is-equiv-map-equiv (eq-transpose-equiv (_ , H) x y))
```

### Being a infinitely coherent equivalence implies being an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-is-infinitely-coherent-equivalence :
    is-infinitely-coherent-equivalence f → is-equiv f
  is-equiv-is-infinitely-coherent-equivalence H =
    is-equiv-is-invertible
      ( map-inv-is-infinitely-coherent-equivalence H)
      ( λ y →
        map-inv-is-infinitely-coherent-equivalence
          ( is-equiv-map-transpose-is-infinitely-coherent-equivalence H _ y)
          (  refl))
      ( λ x →
        inv (map-transpose-is-infinitely-coherent-equivalence H x (f x) refl))
```

### Any map homotopy to an infinitely coherent equivalence is an infinitely coherent equivalence

```agda
is-infinitely-coherent-equivalence-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} →
  f ~ g →
  is-infinitely-coherent-equivalence f → is-infinitely-coherent-equivalence g
map-inv-is-infinitely-coherent-equivalence
  ( is-infinitely-coherent-equivalence-htpy H K) =
  map-inv-is-infinitely-coherent-equivalence K
map-transpose-is-infinitely-coherent-equivalence
  ( is-infinitely-coherent-equivalence-htpy H K) x y =
  map-transpose-is-infinitely-coherent-equivalence K x y ∘ concat (H x) _
is-equiv-map-transpose-is-infinitely-coherent-equivalence
  ( is-infinitely-coherent-equivalence-htpy H K) x y =
  is-infinitely-coherent-equivalence-comp
    ( is-equiv-map-transpose-is-infinitely-coherent-equivalence K x y)
    ( is-infinitely-coherent-equivalence-is-equiv (is-equiv-concat (H x) _))
```

### Homotopies of elements of type `is-infinitely-coherent-equivalence f`

Consider a map `f : A → B` and consider two elements

```text
  H K : is-infinitely-coherent-equivalence f.
```

A {{#concept "homotopy of elments of type `is-infinitely-coherent-equivalence`" Agda=htpy-is-infinitely-coherent-equivalence}} from `H := (h , s , H')` to `K := (k , t , K')` consists of a homotopy

```text
  α₀ : h ~ k,
```

for each `x : A` and `y : B` a homotopy witnessing that the triangle

```text
               (f x = y)
              /         \
       s x y /           \ t x y
            /             \
           ∨               ∨
  (x = h y) --------------> (x = k y)
             p ↦ p ∙ α₀ y
```

commutes, and finally a homotopy of elements of type

```text
  is-infintitely-coherent-equivalence 
```

```agda
record
  htpy-is-infinitely-coherent-equivalence
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
    (H K : is-infinitely-coherent-equivalence f) : UU (l1 ⊔ l2)
  where
  coinductive
  field
    htpy-map-inv-htpy-is-infinitely-coherent-equivalence :
      map-inv-is-infinitely-coherent-equivalence H ~
      map-inv-is-infinitely-coherent-equivalence K
    htpy-map-transpose-htpy-is-infinitely-coherent-equivalence :
      (x : A) (y : B) →
      coherence-triangle-maps
        ( map-transpose-is-infinitely-coherent-equivalence H x y)
        {!!} -- ( concat _ (htpy-map-inv-htpy-is-infinitely-coherent-equivalence y))
        ( map-transpose-is-infinitely-coherent-equivalence K x y)
    infinitely-htpy-htpy-is-infinitely-coherent-equivalence :
      (x : A) (y : B) →
      htpy-is-infinitely-coherent-equivalence
        ( map-transpose-is-infinitely-coherent-equivalence K x y)
        {!!}
        {!!}
      
```

## Operations

```
inv-infinitely-coherent-equivalence :
   {l1 : Level} {A B : UU l1} → A ≃ʰ B → B ≃ʰ A
map (inv-infinitely-coherent-equivalence e) = map-inv e
map-inv (inv-infinitely-coherent-equivalence e) = map e
eq (inv-infinitely-coherent-equivalence e) y x =
  inv-infinitely-coherent-equivalence (eq e x y)
```

## Properties

### Being a infinitely coherent equivalence is a property

```agda
is-prop-is-infinitely-coherent-equivalence :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-prop (is-infinitely-coherent-equivalence f)
is-prop-is-infinitely-coherent-equivalence = {!!}
```


