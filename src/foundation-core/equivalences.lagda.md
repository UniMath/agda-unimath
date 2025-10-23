# Equivalences

```agda
module foundation-core.equivalences where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.invertible-maps
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

An **equivalence** is a map that has a [section](foundation-core.sections.md)
and a (separate) [retraction](foundation-core.retractions.md). This condition is
also called being **biinvertible**.

The condition of biinvertibility may look odd: Why not say that an equivalence
is a map that has a [2-sided inverse](foundation-core.invertible-maps.md)? The
reason is that the condition of invertibility is
[structure](foundation.structure.md), whereas the condition of being
biinvertible is a [property](foundation-core.propositions.md). To quickly see
this: if `f` is an equivalence, then it has up to
[homotopy](foundation-core.homotopies.md) only one section, and it has up to
homotopy only one retraction.

## Definition

### The predicate of being an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-equiv : (A → B) → UU (l1 ⊔ l2)
  is-equiv f = section f × retraction f
```

### Components of a proof of equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  section-is-equiv : section f
  section-is-equiv = pr1 H

  retraction-is-equiv : retraction f
  retraction-is-equiv = pr2 H

  map-section-is-equiv : B → A
  map-section-is-equiv = map-section f section-is-equiv

  map-retraction-is-equiv : B → A
  map-retraction-is-equiv = map-retraction f retraction-is-equiv

  is-section-map-section-is-equiv : is-section f map-section-is-equiv
  is-section-map-section-is-equiv = is-section-map-section f section-is-equiv

  is-retraction-map-retraction-is-equiv :
    is-retraction f map-retraction-is-equiv
  is-retraction-map-retraction-is-equiv =
    is-retraction-map-retraction f retraction-is-equiv
```

### Equivalences

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  equiv : UU (l1 ⊔ l2)
  equiv = Σ (A → B) is-equiv

infix 6 _≃_

_≃_ : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
A ≃ B = equiv A B
```

### Components of an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-equiv : A → B
  map-equiv = pr1 e

  is-equiv-map-equiv : is-equiv map-equiv
  is-equiv-map-equiv = pr2 e

  section-map-equiv : section map-equiv
  section-map-equiv = section-is-equiv is-equiv-map-equiv

  map-section-map-equiv : B → A
  map-section-map-equiv = map-section map-equiv section-map-equiv

  is-section-map-section-map-equiv :
    is-section map-equiv map-section-map-equiv
  is-section-map-section-map-equiv =
    is-section-map-section map-equiv section-map-equiv

  retraction-map-equiv : retraction map-equiv
  retraction-map-equiv = retraction-is-equiv is-equiv-map-equiv

  map-retraction-map-equiv : B → A
  map-retraction-map-equiv = map-retraction map-equiv retraction-map-equiv

  is-retraction-map-retraction-map-equiv :
    is-retraction map-equiv map-retraction-map-equiv
  is-retraction-map-retraction-map-equiv =
    is-retraction-map-retraction map-equiv retraction-map-equiv
```

### The identity equivalence

```agda
module _
  {l : Level} {A : UU l}
  where

  is-equiv-id : is-equiv (id {l} {A})
  pr1 (pr1 is-equiv-id) = id
  pr2 (pr1 is-equiv-id) = refl-htpy
  pr1 (pr2 is-equiv-id) = id
  pr2 (pr2 is-equiv-id) = refl-htpy

  id-equiv : A ≃ A
  pr1 id-equiv = id
  pr2 id-equiv = is-equiv-id
```

## Properties

### A map is invertible if and only if it is an equivalence

**Proof:** It is clear that if a map is
[invertible](foundation-core.invertible-maps.md), then it is also biinvertible,
and hence an equivalence.

For the converse, suppose that `f : A → B` is an equivalence with section
`g : B → A` equipped with `G : f ∘ g ~ id`, and retraction `h : B → A` equipped
with `H : h ∘ f ~ id`. We claim that the map `g : B → A` is also a retraction.
To see this, we concatenate the following homotopies

```text
         H⁻¹ ·r g ·r f                  h ·l G ·r f           H
  g ∘ h ---------------> h ∘ f ∘ g ∘ f -------------> h ∘ f -----> id.
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-is-invertible' : is-invertible f → is-equiv f
  is-equiv-is-invertible' (g , H , K) = ((g , H) , (g , K))

  is-equiv-is-invertible :
    (g : B → A) (H : f ∘ g ~ id) (K : g ∘ f ~ id) → is-equiv f
  is-equiv-is-invertible g H K = is-equiv-is-invertible' (g , H , K)

  is-retraction-map-section-is-equiv :
    (H : is-equiv f) → is-retraction f (map-section-is-equiv H)
  is-retraction-map-section-is-equiv H =
    ( ( inv-htpy
        ( ( is-retraction-map-retraction-is-equiv H) ·r
          ( map-section-is-equiv H ∘ f))) ∙h
      ( map-retraction-is-equiv H ·l is-section-map-section-is-equiv H ·r f)) ∙h
    ( is-retraction-map-retraction-is-equiv H)

  is-invertible-is-equiv : is-equiv f → is-invertible f
  pr1 (is-invertible-is-equiv H) = map-section-is-equiv H
  pr1 (pr2 (is-invertible-is-equiv H)) = is-section-map-section-is-equiv H
  pr2 (pr2 (is-invertible-is-equiv H)) = is-retraction-map-section-is-equiv H
```

### Coherently invertible maps are equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-is-coherently-invertible :
    is-coherently-invertible f → is-equiv f
  is-equiv-is-coherently-invertible H =
    is-equiv-is-invertible' (is-invertible-is-coherently-invertible H)

  is-equiv-is-transpose-coherently-invertible :
    is-transpose-coherently-invertible f → is-equiv f
  is-equiv-is-transpose-coherently-invertible H =
    is-equiv-is-invertible'
      ( is-invertible-is-transpose-coherently-invertible H)
```

The following maps are not simple constructions and should not be computed with.
Therefore, we mark them as `abstract`.

```agda
  abstract
    is-coherently-invertible-is-equiv :
      is-equiv f → is-coherently-invertible f
    is-coherently-invertible-is-equiv =
      is-coherently-invertible-is-invertible ∘ is-invertible-is-equiv

  abstract
    is-transpose-coherently-invertible-is-equiv :
      is-equiv f → is-transpose-coherently-invertible f
    is-transpose-coherently-invertible-is-equiv =
      is-transpose-coherently-invertible-is-invertible ∘ is-invertible-is-equiv
```

### Structure obtained from being coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  map-inv-is-equiv : B → A
  map-inv-is-equiv = pr1 (is-invertible-is-equiv H)

  is-section-map-inv-is-equiv : is-section f map-inv-is-equiv
  is-section-map-inv-is-equiv =
    is-section-map-inv-is-coherently-invertible-is-invertible
      ( is-invertible-is-equiv H)

  is-retraction-map-inv-is-equiv : is-retraction f map-inv-is-equiv
  is-retraction-map-inv-is-equiv =
    is-retraction-map-inv-is-coherently-invertible-is-invertible
      ( is-invertible-is-equiv H)

  coherence-map-inv-is-equiv :
    coherence-is-coherently-invertible f
      ( map-inv-is-equiv)
      ( is-section-map-inv-is-equiv)
      ( is-retraction-map-inv-is-equiv)
  coherence-map-inv-is-equiv =
    coh-is-coherently-invertible-is-invertible (is-invertible-is-equiv H)

  is-equiv-map-inv-is-equiv : is-equiv map-inv-is-equiv
  is-equiv-map-inv-is-equiv =
    is-equiv-is-invertible f
      ( is-retraction-map-inv-is-equiv)
      ( is-section-map-inv-is-equiv)
```

### The inverse of an equivalence is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = map-inv-is-equiv (is-equiv-map-equiv e)

  is-section-map-inv-equiv : is-section (map-equiv e) map-inv-equiv
  is-section-map-inv-equiv = is-section-map-inv-is-equiv (is-equiv-map-equiv e)

  is-retraction-map-inv-equiv : is-retraction (map-equiv e) map-inv-equiv
  is-retraction-map-inv-equiv =
    is-retraction-map-inv-is-equiv (is-equiv-map-equiv e)

  coherence-map-inv-equiv :
    coherence-is-coherently-invertible
      ( map-equiv e)
      ( map-inv-equiv)
      ( is-section-map-inv-equiv)
      ( is-retraction-map-inv-equiv)
  coherence-map-inv-equiv =
    coherence-map-inv-is-equiv (is-equiv-map-equiv e)

  is-equiv-map-inv-equiv : is-equiv map-inv-equiv
  is-equiv-map-inv-equiv = is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

  inv-equiv : B ≃ A
  pr1 inv-equiv = map-inv-equiv
  pr2 inv-equiv = is-equiv-map-inv-equiv
```

### The 3-for-2 property of equivalences

The **3-for-2 property** of equivalences asserts that for any
[commuting triangle](foundation-core.commuting-triangles-of-maps.md) of maps

```text
       h
  A ------> B
   \       /
   f\     /g
     \   /
      ∨ ∨
       X,
```

if two of the three maps are equivalences, then so is the third.

We also record special cases of the 3-for-2 property of equivalences, where we
only assume maps `g : B → X` and `h : A → B`. In this special case, we set
`f := g ∘ h` and the triangle commutes by `refl-htpy`.

[André Joyal](https://en.wikipedia.org/wiki/André_Joyal) proposed calling this
property the 3-for-2 property, despite most mathematicians calling it the
_2-out-of-3 property_. The story goes that on the produce market is is common to
advertise a discount as "3-for-2". If you buy two apples, then you get the third
for free. Similarly, if you prove that two maps in a commuting triangle are
equivalences, then you get the third for free.

#### The left map in a commuting triangle is an equivalence if the other two maps are equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (T : f ~ g ∘ h)
  where

  abstract
    is-equiv-left-map-triangle : is-equiv h → is-equiv g → is-equiv f
    pr1 (is-equiv-left-map-triangle H G) =
      section-left-map-triangle f g h T
        ( section-is-equiv H)
        ( section-is-equiv G)
    pr2 (is-equiv-left-map-triangle H G) =
      retraction-left-map-triangle f g h T
        ( retraction-is-equiv G)
        ( retraction-is-equiv H)
```

#### The right map in a commuting triangle is an equivalence if the other two maps are equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  abstract
    is-equiv-right-map-triangle :
      is-equiv f → is-equiv h → is-equiv g
    is-equiv-right-map-triangle
      ( section-f , retraction-f)
      ( (sh , is-section-sh) , retraction-h) =
        ( pair
          ( section-right-map-triangle f g h H section-f)
          ( retraction-left-map-triangle g f sh
            ( inv-htpy
              ( ( H ·r map-section h (sh , is-section-sh)) ∙h
                ( g ·l is-section-map-section h (sh , is-section-sh))))
            ( retraction-f)
            ( h , is-section-sh)))
```

#### If the left and right maps in a commuting triangle are equivalences, then the top map is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  section-is-equiv-top-map-triangle :
    is-equiv g → is-equiv f → section h
  section-is-equiv-top-map-triangle G F =
    section-left-map-triangle h
      ( map-retraction-is-equiv G)
      ( f)
      ( inv-htpy
        ( ( map-retraction g (retraction-is-equiv G) ·l H) ∙h
          ( is-retraction-map-retraction g (retraction-is-equiv G) ·r h)))
      ( section-is-equiv F)
      ( g , is-retraction-map-retraction-is-equiv G)

  map-section-is-equiv-top-map-triangle :
    is-equiv g → is-equiv f → B → A
  map-section-is-equiv-top-map-triangle G F =
    map-section h (section-is-equiv-top-map-triangle G F)

  abstract
    is-equiv-top-map-triangle :
      is-equiv g → is-equiv f → is-equiv h
    is-equiv-top-map-triangle
      ( section-g , (rg , is-retraction-rg))
      ( section-f , retraction-f) =
      ( pair
        ( section-left-map-triangle h rg f
          ( inv-htpy
            ( ( map-retraction g (rg , is-retraction-rg) ·l H) ∙h
              ( is-retraction-map-retraction g (rg , is-retraction-rg) ·r h)))
          ( section-f)
          ( g , is-retraction-rg))
        ( retraction-top-map-triangle f g h H retraction-f))
```

#### Composites of equivalences are equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  opaque
    is-equiv-comp :
      (g : B → X) (h : A → B) → is-equiv h → is-equiv g → is-equiv (g ∘ h)
    pr1 (is-equiv-comp g h (sh , rh) (sg , rg)) = section-comp g h sh sg
    pr2 (is-equiv-comp g h (sh , rh) (sg , rg)) = retraction-comp g h rg rh

  comp-equiv : B ≃ X → A ≃ B → A ≃ X
  pr1 (comp-equiv g h) = map-equiv g ∘ map-equiv h
  pr2 (comp-equiv g h) = is-equiv-comp (pr1 g) (pr1 h) (pr2 h) (pr2 g)

  infixr 15 _∘e_
  _∘e_ : B ≃ X → A ≃ B → A ≃ X
  _∘e_ = comp-equiv
```

#### If a composite and its right factor are equivalences, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-equiv-left-factor :
    (g : B → X) (h : A → B) →
    is-equiv (g ∘ h) → is-equiv h → is-equiv g
  is-equiv-left-factor g h is-equiv-gh is-equiv-h =
      is-equiv-right-map-triangle (g ∘ h) g h refl-htpy is-equiv-gh is-equiv-h
```

#### If a composite and its left factor are equivalences, then so is its right factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  is-equiv-right-factor :
    (g : B → X) (h : A → B) →
    is-equiv g → is-equiv (g ∘ h) → is-equiv h
  is-equiv-right-factor g h is-equiv-g is-equiv-gh =
    is-equiv-top-map-triangle (g ∘ h) g h refl-htpy is-equiv-g is-equiv-gh
```

### Equivalences are closed under homotopies

We show that if `f ~ g`, then `f` is an equivalence if and only if `g` is an
equivalence. Furthermore, we show that if `f` and `g` are homotopic equivaleces,
then their inverses are also homotopic.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-htpy :
      {f : A → B} (g : A → B) → f ~ g → is-equiv g → is-equiv f
    pr1 (pr1 (is-equiv-htpy g G ((h , H) , (k , K)))) = h
    pr2 (pr1 (is-equiv-htpy g G ((h , H) , (k , K)))) = (G ·r h) ∙h H
    pr1 (pr2 (is-equiv-htpy g G ((h , H) , (k , K)))) = k
    pr2 (pr2 (is-equiv-htpy g G ((h , H) , (k , K)))) = (k ·l G) ∙h K

  is-equiv-htpy-equiv : {f : A → B} (e : A ≃ B) → f ~ map-equiv e → is-equiv f
  is-equiv-htpy-equiv e H = is-equiv-htpy (map-equiv e) H (is-equiv-map-equiv e)

  abstract
    is-equiv-htpy' : (f : A → B) {g : A → B} → f ~ g → is-equiv f → is-equiv g
    is-equiv-htpy' f H = is-equiv-htpy f (inv-htpy H)

  is-equiv-htpy-equiv' : (e : A ≃ B) {g : A → B} → map-equiv e ~ g → is-equiv g
  is-equiv-htpy-equiv' e H =
    is-equiv-htpy' (map-equiv e) H (is-equiv-map-equiv e)

  htpy-map-inv-is-equiv :
    {f g : A → B} (H : f ~ g) (F : is-equiv f) (G : is-equiv g) →
    map-inv-is-equiv F ~ map-inv-is-equiv G
  htpy-map-inv-is-equiv H F G =
    htpy-map-inv-is-invertible H
      ( is-invertible-is-equiv F)
      ( is-invertible-is-equiv G)

is-equiv-htpy-id : {l : Level} {A : UU l} {f : A → A} → f ~ id → is-equiv f
is-equiv-htpy-id H = is-equiv-htpy id H is-equiv-id

is-equiv-htpy-id' : {l : Level} {A : UU l} {f : A → A} → id ~ f → is-equiv f
is-equiv-htpy-id' H = is-equiv-htpy' id H is-equiv-id
```

### Any retraction of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-retraction :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
    is-equiv f → (g ∘ f) ~ id → is-equiv g
  is-equiv-is-retraction {A = A} {f = f} {g = g} is-equiv-f H =
    is-equiv-right-map-triangle id g f (inv-htpy H) is-equiv-id is-equiv-f
```

### Any section of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-section :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A} →
    is-equiv f → f ∘ g ~ id → is-equiv g
  is-equiv-is-section {B = B} {f = f} {g = g} is-equiv-f H =
    is-equiv-top-map-triangle id f g (inv-htpy H) is-equiv-f is-equiv-id
```

### If a section of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-is-equiv-section :
      (s : section f) → is-equiv (map-section f s) → is-equiv f
    is-equiv-is-equiv-section (g , G) S = is-equiv-is-retraction S G
```

### If a retraction of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-is-equiv-retraction :
      (r : retraction f) → is-equiv (map-retraction f r) → is-equiv f
    is-equiv-is-equiv-retraction (g , G) R = is-equiv-is-section R G
```

### Any section of an equivalence is homotopic to its inverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  htpy-map-inv-equiv-section :
    (f : section (map-equiv e)) → map-inv-equiv e ~ map-section (map-equiv e) f
  htpy-map-inv-equiv-section (f , H) =
    (map-inv-equiv e ·l inv-htpy H) ∙h (is-retraction-map-inv-equiv e ·r f)
```

### Any retraction of an equivalence is homotopic to its inverse

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  htpy-map-inv-equiv-retraction :
    (f : retraction (map-equiv e)) →
    map-inv-equiv e ~ map-retraction (map-equiv e) f
  htpy-map-inv-equiv-retraction (f , H) =
    (inv-htpy H ·r map-inv-equiv e) ∙h (f ·l is-section-map-inv-equiv e)
```

### Equivalences in commuting squares

```agda
is-equiv-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv g → is-equiv f
is-equiv-equiv {f = f} {g} i j H K =
  is-equiv-right-factor
    ( map-equiv j)
    ( f)
    ( is-equiv-map-equiv j)
    ( is-equiv-left-map-triangle
      ( map-equiv j ∘ f)
      ( g)
      ( map-equiv i)
      ( H)
      ( is-equiv-map-equiv i)
      ( K))

is-equiv-equiv' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv f → is-equiv g
is-equiv-equiv' {f = f} {g} i j H K =
  is-equiv-left-factor
    ( g)
    ( map-equiv i)
    ( is-equiv-left-map-triangle
      ( g ∘ map-equiv i)
      ( map-equiv j)
      ( f)
      ( inv-htpy H)
      ( K)
      ( is-equiv-map-equiv j))
    ( is-equiv-map-equiv i)
```

We will assume a commuting square

```text
        h
    A -----> C
    |        |
  f |        | g
    ∨        ∨
    B -----> D
        i
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h))
  where

  abstract
    is-equiv-top-is-equiv-left-square :
      is-equiv i → is-equiv f → is-equiv g → is-equiv h
    is-equiv-top-is-equiv-left-square Ei Ef Eg =
      is-equiv-top-map-triangle (i ∘ f) g h H Eg (is-equiv-comp i f Ef Ei)

  abstract
    is-equiv-top-is-equiv-bottom-square :
      is-equiv f → is-equiv g → is-equiv i → is-equiv h
    is-equiv-top-is-equiv-bottom-square Ef Eg Ei =
      is-equiv-top-map-triangle (i ∘ f) g h H Eg (is-equiv-comp i f Ef Ei)

  abstract
    is-equiv-bottom-is-equiv-top-square :
      is-equiv f → is-equiv g → is-equiv h → is-equiv i
    is-equiv-bottom-is-equiv-top-square Ef Eg Eh =
      is-equiv-left-factor i f
        ( is-equiv-left-map-triangle (i ∘ f) g h H Eh Eg)
        ( Ef)

  abstract
    is-equiv-left-is-equiv-right-square :
      is-equiv h → is-equiv i → is-equiv g → is-equiv f
    is-equiv-left-is-equiv-right-square Eh Ei Eg =
      is-equiv-right-factor i f Ei
        ( is-equiv-left-map-triangle (i ∘ f) g h H Eh Eg)

  abstract
    is-equiv-right-is-equiv-left-square :
      is-equiv h → is-equiv i → is-equiv f → is-equiv g
    is-equiv-right-is-equiv-left-square Eh Ei Ef =
      is-equiv-right-map-triangle (i ∘ f) g h H (is-equiv-comp i f Ef Ei) Eh
```

### Equivalences are embeddings

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-emb-is-equiv :
      {f : A → B} → is-equiv f → (x y : A) → is-equiv (ap f {x} {y})
    is-emb-is-equiv H x y =
      is-equiv-is-invertible'
        ( is-invertible-ap-is-coherently-invertible
          ( is-coherently-invertible-is-equiv H))

  equiv-ap :
    (e : A ≃ B) (x y : A) → (x ＝ y) ≃ (map-equiv e x ＝ map-equiv e y)
  pr1 (equiv-ap e x y) = ap (map-equiv e)
  pr2 (equiv-ap e x y) = is-emb-is-equiv (is-equiv-map-equiv e) x y

  map-inv-equiv-ap :
    (e : A ≃ B) (x y : A) → map-equiv e x ＝ map-equiv e y → x ＝ y
  map-inv-equiv-ap e x y = map-inv-equiv (equiv-ap e x y)
```

## Equivalence reasoning

Equivalences can be constructed by equational reasoning in the following way:

```text
equivalence-reasoning
  X ≃ Y by equiv-1
    ≃ Z by equiv-2
    ≃ V by equiv-3
```

The equivalence constructed in this way is `equiv-1 ∘e (equiv-2 ∘e equiv-3)`,
i.e., the equivivalence is associated fully to the right.

**Note.** In situations where it is important to have precise control over an
equivalence or its inverse, it is often better to avoid making use of
equivalence reasoning. For example, since many of the entries proving that a map
is an equivalence are marked as `abstract` in agda-unimath, the inverse of an
equivalence often does not compute to any map that one might expect the inverse
to be. If inverses of equivalences are used in equivalence reasoning, this
results in a composed equivalence that also does not compute to any expected
underlying map.

Even if a proof by equivalence reasoning is clear to the human reader,
constructing equivalences by hand by constructing maps back and forth and two
homotopies witnessing that they are mutual inverses is often the most
straightforward solution that gives the best expected computational behavior of
the constructed equivalence. In particular, if the underlying map or its inverse
are noteworthy maps, it is good practice to define them directly rather than as
underlying maps of equivalences constructed by equivalence reasoning.

```agda
infixl 1 equivalence-reasoning_
infixl 0 step-equivalence-reasoning

equivalence-reasoning_ :
  {l1 : Level} (X : UU l1) → X ≃ X
equivalence-reasoning X = id-equiv

step-equivalence-reasoning :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} →
  (X ≃ Y) → (Z : UU l3) → (Y ≃ Z) → (X ≃ Z)
step-equivalence-reasoning e Z f = f ∘e e

syntax step-equivalence-reasoning e Z f = e ≃ Z by f
```

## See also

- For the notion of coherently invertible maps, also known as half-adjoint
  equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
- For the notion of finitely coherent equivalence, see
  [`foundation.finitely-coherent-equivalence`)(foundation.finitely-coherent-equivalence.md).
- For the notion of finitely coherently invertible map, see
  [`foundation.finitely-coherently-invertible-map`)(foundation.finitely-coherently-invertible-map.md).
- For the notion of infinitely coherent equivalence, see
  [`foundation.infinitely-coherent-equivalences`](foundation.infinitely-coherent-equivalences.md).

### Table of files about function types, composition, and equivalences

{{#include tables/composition.md}}
