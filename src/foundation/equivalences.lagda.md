# Equivalences

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.equivalences where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coherently-invertible-maps using
  ( has-inverse; is-coherently-invertible; is-coherently-invertible-has-inverse;
    issec-inv-has-inverse; isretr-inv-has-inverse; coherence-inv-has-inverse)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.function-extensionality using ()
open import foundation.functions using (id; _∘_)
open import foundation.foundation-base using ([is-equiv]; _[≃]_; [sec])
open import foundation.homotopies using
  ( _~_; refl-htpy; _∙h_; inv-htpy; _·r_; _·l_; htpy-right-whisk)
open import foundation.identity-types using
  ( Id; refl; concat; concat'; _∙_; inv; ap; tr; inv-inv; inv-con; con-inv;
    right-unit)
open import foundation.retractions using (retr)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

An equivalence is a map that has a section and a (separate) retraction. This may look odd: Why not say that an equivalence is a map that has a 2-sided inverse? The reason is that the latter requirement would put nontrivial structure on the map, whereas having the section and retraction separate yields a property. To quickly see this: if `f` is an equivalence, then it has up to homotopy only one section, and it has up to homotopy only one retraction. 

## Definition

### Equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where
  
  is-equiv : (A → B) → UU (l1 ⊔ l2)
  is-equiv = [is-equiv]

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = A [≃] B
```

### Families of equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where
  
  is-fiberwise-equiv : (f : (x : A) → B x → C x) → UU (l1 ⊔ l2 ⊔ l3)
  is-fiberwise-equiv f = (x : A) → is-equiv (f x)
```

### Immediate structure of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-equiv : (A ≃ B) → (A → B)
  map-equiv e = pr1 e

  is-equiv-map-equiv : (e : A ≃ B) → is-equiv (map-equiv e)
  is-equiv-map-equiv e = pr2 e
```

## Examples

### The identity map is an equivalence

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

### A map has an two-sided inverse if and only if it is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-equiv-has-inverse' : has-inverse f → is-equiv f
  pr1 (pr1 (is-equiv-has-inverse' (pair g (pair H K)))) = g
  pr2 (pr1 (is-equiv-has-inverse' (pair g (pair H K)))) = H
  pr1 (pr2 (is-equiv-has-inverse' (pair g (pair H K)))) = g
  pr2 (pr2 (is-equiv-has-inverse' (pair g (pair H K)))) = K

  is-equiv-has-inverse :
    (g : B → A) (H : (f ∘ g) ~ id) (K : (g ∘ f) ~ id) → is-equiv f
  is-equiv-has-inverse g H K =
    is-equiv-has-inverse' (pair g (pair H K))

  has-inverse-is-equiv : is-equiv f → has-inverse f
  pr1 (has-inverse-is-equiv  (pair (pair g G) (pair h H))) = g
  pr1 (pr2 (has-inverse-is-equiv (pair (pair g G) (pair h H)))) = G
  pr2 (pr2 (has-inverse-is-equiv (pair (pair g G) (pair h H)))) =
    (((inv-htpy (H ·r g)) ∙h (h ·l G)) ·r f) ∙h H
```

## Properties

### Coherently invertible maps are equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-coherently-invertible-is-equiv : is-equiv f → is-coherently-invertible f
    is-coherently-invertible-is-equiv =
      is-coherently-invertible-has-inverse ∘ has-inverse-is-equiv

  abstract
    is-equiv-is-coherently-invertible :
      is-coherently-invertible f → is-equiv f
    is-equiv-is-coherently-invertible (pair g (pair G (pair H K))) =
      is-equiv-has-inverse g G H
```

### Structure obtained from being coherently invertible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (H : is-equiv f)
  where

  map-inv-is-equiv : B → A
  map-inv-is-equiv = pr1 (has-inverse-is-equiv H)

  issec-map-inv-is-equiv : (f ∘ map-inv-is-equiv) ~ id
  issec-map-inv-is-equiv = issec-inv-has-inverse (has-inverse-is-equiv H)

  isretr-map-inv-is-equiv : (map-inv-is-equiv ∘ f) ~ id
  isretr-map-inv-is-equiv =
    isretr-inv-has-inverse (has-inverse-is-equiv H)
  
  coherence-map-inv-is-equiv :
    ( issec-map-inv-is-equiv ·r f) ~ (f ·l isretr-map-inv-is-equiv)
  coherence-map-inv-is-equiv =
    coherence-inv-has-inverse (has-inverse-is-equiv H)

  is-equiv-map-inv-is-equiv : is-equiv map-inv-is-equiv
  is-equiv-map-inv-is-equiv =
    is-equiv-has-inverse f
      ( isretr-map-inv-is-equiv)
      ( issec-map-inv-is-equiv)
```

### The inverse of an equivalence is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : A ≃ B)
  where

  map-inv-equiv : B → A
  map-inv-equiv = map-inv-is-equiv (is-equiv-map-equiv e)

  issec-map-inv-equiv : ((map-equiv e) ∘ map-inv-equiv) ~ id
  issec-map-inv-equiv = issec-map-inv-is-equiv (is-equiv-map-equiv e)

  isretr-map-inv-equiv : (map-inv-equiv ∘ (map-equiv e)) ~ id
  isretr-map-inv-equiv =
    isretr-map-inv-is-equiv (is-equiv-map-equiv e)
  
  coherence-map-inv-equiv :
    ( issec-map-inv-equiv ·r (map-equiv e)) ~
    ( (map-equiv e) ·l isretr-map-inv-equiv)
  coherence-map-inv-equiv =
    coherence-map-inv-is-equiv (is-equiv-map-equiv e)

  is-equiv-map-inv-equiv : is-equiv map-inv-equiv
  is-equiv-map-inv-equiv = is-equiv-map-inv-is-equiv (is-equiv-map-equiv e)

  inv-equiv : B ≃ A
  pr1 inv-equiv = map-inv-equiv
  pr2 inv-equiv = is-equiv-map-inv-equiv
```

### Equivalences are closed under homotopies

We show that if `f ~ g`, then `f` is an equivalence if and only if `g` is an equivalence. Furthermore, we show that if `f` and `g` are homotopic equivaleces, then their inverses are also homotopic.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-htpy :
      {f : A → B} (g : A → B) → f ~ g → is-equiv g → is-equiv f
    pr1 (pr1 (is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)))) = gs
    pr2 (pr1 (is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)))) =
      (H ·r gs) ∙h issec
    pr1 (pr2 (is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)))) = gr
    pr2 (pr2 (is-equiv-htpy g H (pair (pair gs issec) (pair gr isretr)))) =
      (gr ·l H) ∙h isretr

  is-equiv-htpy-equiv : {f : A → B} (e : A ≃ B) → f ~ map-equiv e → is-equiv f
  is-equiv-htpy-equiv e H = is-equiv-htpy (map-equiv e) H (is-equiv-map-equiv e)

  abstract
    is-equiv-htpy' : (f : A → B) {g : A → B} → f ~ g → is-equiv f → is-equiv g
    is-equiv-htpy' f H = is-equiv-htpy f (inv-htpy H)

  is-equiv-htpy-equiv' : (e : A ≃ B) {g : A → B} → map-equiv e ~ g → is-equiv g
  is-equiv-htpy-equiv' e H =
    is-equiv-htpy' (map-equiv e) H (is-equiv-map-equiv e)

  -- Note: This should probably be called `htpy-map-inv-is-equiv`
  inv-htpy-is-equiv :
    {f g : A → B} (G : f ~ g) (H : is-equiv f) (K : is-equiv g) →
    (map-inv-is-equiv H) ~ (map-inv-is-equiv K)
  inv-htpy-is-equiv G H K b =
    ( inv
      ( isretr-map-inv-is-equiv K (map-inv-is-equiv H b))) ∙
    ( ap (map-inv-is-equiv K)
      ( ( inv (G (map-inv-is-equiv H b))) ∙
        ( issec-map-inv-is-equiv H b)))
```

### The 3-for-2 property of equivalences

#### Composites of equivalences are equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  triangle-section : (S : [sec] h) → g ~ (f ∘ (pr1 S))
  triangle-section (pair s issec) = inv-htpy ((H ·r s) ∙h (g ·l issec))

  section-comp : [sec] h → [sec] f → [sec] g
  pr1 (section-comp sec-h sec-f) = h ∘ (pr1 sec-f)
  pr2 (section-comp sec-h sec-f) = (inv-htpy (H ·r (pr1 sec-f))) ∙h (pr2 sec-f)
  
  section-comp' : [sec] h → [sec] g → [sec] f
  pr1 (section-comp' sec-h sec-g) = (pr1 sec-h) ∘ (pr1 sec-g)
  pr2 (section-comp' sec-h sec-g) =
    ( H ·r ((pr1 sec-h) ∘ (pr1 sec-g))) ∙h
    ( ( g ·l ((pr2 sec-h) ·r (pr1 sec-g))) ∙h ((pr2 sec-g)))

  triangle-retraction : (R : retr g) → h ~ ((pr1 R) ∘ f)
  triangle-retraction (pair r isretr) = inv-htpy ((r ·l H) ∙h (isretr ·r h))

  retraction-comp : retr g → retr f → retr h
  pr1 (retraction-comp retr-g retr-f) = (pr1 retr-f) ∘ g
  pr2 (retraction-comp retr-g retr-f) =
    (inv-htpy ((pr1 retr-f) ·l H)) ∙h (pr2 retr-f)

  retraction-comp' : retr g → retr h → retr f
  pr1 (retraction-comp' retr-g retr-h) = (pr1 retr-h) ∘ (pr1 retr-g)
  pr2 (retraction-comp' retr-g retr-h) =
    ( ((pr1 retr-h) ∘ (pr1 retr-g)) ·l H) ∙h
    ( ((pr1 retr-h) ·l ((pr2 retr-g) ·r h)) ∙h (pr2 retr-h))

  abstract
    is-equiv-comp : is-equiv h → is-equiv g → is-equiv f
    pr1 (is-equiv-comp (pair sec-h retr-h) (pair sec-g retr-g)) =
      section-comp' sec-h sec-g
    pr2 (is-equiv-comp (pair sec-h retr-h) (pair sec-g retr-g)) =
      retraction-comp' retr-g retr-h

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-equiv-comp' :
      (g : B → X) (h : A → B) → is-equiv h → is-equiv g → is-equiv (g ∘ h)
    is-equiv-comp' g h = is-equiv-comp (g ∘ h) g h refl-htpy

  equiv-comp : (B ≃ X) → (A ≃ B) → (A ≃ X)
  pr1 (equiv-comp g h) = (pr1 g) ∘ (pr1 h)
  pr2 (equiv-comp g h) = is-equiv-comp' (pr1 g) (pr1 h) (pr2 h) (pr2 g)

  _∘e_ : (B ≃ X) → (A ≃ B) → (A ≃ X)
  _∘e_ = equiv-comp
```

#### If a composite and its right factor are equivalences, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where
  
  abstract
    is-equiv-left-factor : is-equiv f → is-equiv h → is-equiv g
    pr1
      ( is-equiv-left-factor
        ( pair sec-f retr-f)
        ( pair (pair sh sh-issec) retr-h)) =
      section-comp f g h H (pair sh sh-issec) sec-f
    pr2
      ( is-equiv-left-factor
        ( pair sec-f retr-f)
        ( pair (pair sh sh-issec) retr-h)) =
      retraction-comp' g f sh
        ( triangle-section f g h H (pair sh sh-issec))
        ( retr-f)
        ( pair h sh-issec)
```

#### If a composite and its left factor are equivalences, then so is its right factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-equiv-right-factor : is-equiv g → is-equiv f → is-equiv h
    pr1
      ( is-equiv-right-factor
        ( pair sec-g (pair rg rg-isretr))
        ( pair sec-f retr-f)) =
      section-comp' h rg f
        ( triangle-retraction f g h H (pair rg rg-isretr))
        ( sec-f)
        ( pair g rg-isretr)
    pr2
      ( is-equiv-right-factor
        ( pair sec-g (pair rg rg-isretr))
        ( pair sec-f retr-f)) =
      retraction-comp f g h H (pair rg rg-isretr) retr-f
```

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-equiv-left-factor' :
      (g : B → X) (h : A → B) → is-equiv (g ∘ h) → is-equiv h → is-equiv g
    is-equiv-left-factor' g h = is-equiv-left-factor (g ∘ h) g h refl-htpy

  abstract
    is-equiv-right-factor' :
      (g : B → X) (h : A → B) → is-equiv g → is-equiv (g ∘ h) → is-equiv h
    is-equiv-right-factor' g h = is-equiv-right-factor (g ∘ h) g h refl-htpy
```

### Any retraction of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-retraction :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f  → (g ∘ f) ~ id → is-equiv g
  is-equiv-is-retraction {A = A} {f = f} {g = g} is-equiv-f H =
    is-equiv-left-factor id g f (inv-htpy H) is-equiv-id is-equiv-f
```

### Any section of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-section :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f → (f ∘ g) ~ id → is-equiv g
  is-equiv-is-section {B = B} {f = f} {g = g} is-equiv-f H =
    is-equiv-right-factor id f g (inv-htpy H) is-equiv-f is-equiv-id
```

### If a section of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-sec-is-equiv :
      ( sec-f : [sec] f) → is-equiv (pr1 sec-f) → is-equiv f
    is-equiv-sec-is-equiv (pair g issec-g) is-equiv-sec-f =
      is-equiv-htpy h
        ( ( f ·l (inv-htpy (issec-map-inv-is-equiv is-equiv-sec-f))) ∙h
          ( htpy-right-whisk issec-g h))
        ( is-equiv-map-inv-is-equiv is-equiv-sec-f)
      where
      h : A → B
      h = map-inv-is-equiv is-equiv-sec-f
```

### Equivalences in commuting squares

```agda
is-equiv-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (i : A ≃ X) (j : B ≃ Y)
  (H : (map-equiv j ∘ f) ~ (g ∘ map-equiv i)) → is-equiv g → is-equiv f
is-equiv-equiv {f = f} {g} i j H K =
  is-equiv-right-factor'
    ( map-equiv j)
    ( f)
    ( is-equiv-map-equiv j)
    ( is-equiv-comp
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
  is-equiv-left-factor'
    ( g)
    ( map-equiv i)
    ( is-equiv-comp
      ( g ∘ map-equiv i)
      ( map-equiv j)
      ( f)
      ( inv-htpy H)
      ( K)
      ( is-equiv-map-equiv j))
    ( is-equiv-map-equiv i)
```

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → B) (g : C → D) (h : A → C) (i : B → D) (H : (i ∘ f) ~ (g ∘ h))
  where

  {-

  We assumed a commuting square

          h
    A --------> C
    |           |
   f|           |g
    V           V
    B --------> D
          i                                                                   -}
          
  abstract
    is-equiv-top-is-equiv-left-square :
      is-equiv i → is-equiv f → is-equiv g → is-equiv h
    is-equiv-top-is-equiv-left-square Ei Ef Eg =
      is-equiv-right-factor (i ∘ f) g h H Eg (is-equiv-comp' i f Ef Ei)

  abstract
    is-equiv-top-is-equiv-bottom-square :
      is-equiv f → is-equiv g → is-equiv i → is-equiv h
    is-equiv-top-is-equiv-bottom-square Ef Eg Ei =
      is-equiv-right-factor (i ∘ f) g h H Eg (is-equiv-comp' i f Ef Ei)

  abstract
    is-equiv-bottom-is-equiv-top-square :
      is-equiv f → is-equiv g → is-equiv h → is-equiv i
    is-equiv-bottom-is-equiv-top-square Ef Eg Eh = 
      is-equiv-left-factor' i f (is-equiv-comp (i ∘ f) g h H Eh Eg) Ef

  abstract
    is-equiv-left-is-equiv-right-square :
      is-equiv h → is-equiv i → is-equiv g → is-equiv f
    is-equiv-left-is-equiv-right-square Eh Ei Eg =
      is-equiv-right-factor' i f Ei (is-equiv-comp (i ∘ f) g h H Eh Eg)

  abstract
    is-equiv-right-is-equiv-left-square :
      is-equiv h → is-equiv i → is-equiv f → is-equiv g
    is-equiv-right-is-equiv-left-square Eh Ei Ef =
      is-equiv-left-factor (i ∘ f) g h H (is-equiv-comp' i f Ef Ei) Eh
```

## Examples

### The groupoidal operations on identity types are equivalences

```agda
module _
  {l : Level} {A : UU l}
  where
  
  abstract
    is-equiv-inv : (x y : A) → is-equiv (λ (p : Id x y) → inv p)
    is-equiv-inv x y = is-equiv-has-inverse inv inv-inv inv-inv

  equiv-inv : (x y : A) → (Id x y) ≃ (Id y x)
  pr1 (equiv-inv x y) = inv
  pr2 (equiv-inv x y) = is-equiv-inv x y

  inv-concat : {x y : A} (p : Id x y) (z : A) → Id x z → Id y z
  inv-concat p = concat (inv p)

  isretr-inv-concat :
    {x y : A} (p : Id x y) (z : A) → (inv-concat p z ∘ concat p z) ~ id
  isretr-inv-concat refl z q = refl

  issec-inv-concat :
    {x y : A} (p : Id x y) (z : A) → (concat p z ∘ inv-concat p z) ~ id
  issec-inv-concat refl z refl = refl

  abstract
    is-equiv-concat :
      {x y : A} (p : Id x y) (z : A) → is-equiv (concat p z)
    is-equiv-concat p z =
      is-equiv-has-inverse
        ( inv-concat p z)
        ( issec-inv-concat p z)
        ( isretr-inv-concat p z)

  equiv-concat :
    {x y : A} (p : Id x y) (z : A) → Id y z ≃ Id x z
  pr1 (equiv-concat p z) = concat p z
  pr2 (equiv-concat p z) = is-equiv-concat p z
  
  inv-concat' : (x : A) {y z : A} → Id y z → Id x z → Id x y
  inv-concat' x q = concat' x (inv q)

  isretr-inv-concat' :
    (x : A) {y z : A} (q : Id y z) → (inv-concat' x q ∘ concat' x q) ~ id
  isretr-inv-concat' x refl refl = refl

  issec-inv-concat' :
    (x : A) {y z : A} (q : Id y z) → (concat' x q ∘ inv-concat' x q) ~ id
  issec-inv-concat' x refl refl = refl

  abstract
    is-equiv-concat' :
      (x : A) {y z : A} (q : Id y z) → is-equiv (concat' x q)
    is-equiv-concat' x q =
      is-equiv-has-inverse
        ( inv-concat' x q)
        ( issec-inv-concat' x q)
        ( isretr-inv-concat' x q)
  
  equiv-concat' :
    (x : A) {y z : A} (q : Id y z) → Id x y ≃ Id x z
  pr1 (equiv-concat' x q) = concat' x q
  pr2 (equiv-concat' x q) = is-equiv-concat' x q

convert-eq-values-htpy :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f g : A → B} (H : f ~ g)
  (x y : A) → Id (f x) (f y) ≃ Id (g x) (g y)
convert-eq-values-htpy {f = f} {g} H x y =
  ( equiv-concat' (g x) (H y)) ∘e (equiv-concat (inv (H x)) (f y))

module _
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  where

  inv-tr : Id x y → B y → B x
  inv-tr p = tr B (inv p)

  isretr-inv-tr : (p : Id x y) → ((inv-tr p ) ∘ (tr B p)) ~ id
  isretr-inv-tr refl b = refl

  issec-inv-tr : (p : Id x y) → ((tr B p) ∘ (inv-tr p)) ~ id
  issec-inv-tr refl b = refl

  abstract
    is-equiv-tr : (p : Id x y) → is-equiv (tr B p)
    is-equiv-tr p =
      is-equiv-has-inverse
        ( inv-tr p)
        ( issec-inv-tr p)
        ( isretr-inv-tr p)

  equiv-tr : Id x y → (B x) ≃ (B y)
  pr1 (equiv-tr p) = tr B p
  pr2 (equiv-tr p) = is-equiv-tr p

module _
  {l : Level} {A : UU l} {x y z : A}
  where

  abstract
    is-equiv-inv-con :
      (p : Id x y) (q : Id y z) (r : Id x z) → is-equiv (inv-con p q r)
    is-equiv-inv-con refl q r = is-equiv-id

  equiv-inv-con :
    (p : Id x y) (q : Id y z) (r : Id x z) → Id (p ∙ q) r ≃ Id q ((inv p) ∙ r)
  pr1 (equiv-inv-con p q r) = inv-con p q r
  pr2 (equiv-inv-con p q r) = is-equiv-inv-con p q r

  abstract
    is-equiv-con-inv :
      (p : Id x y) (q : Id y z) (r : Id x z) → is-equiv (con-inv p q r)
    is-equiv-con-inv p refl r =
      is-equiv-comp'
        ( concat' p (inv right-unit))
        ( concat (inv right-unit) r)
        ( is-equiv-concat (inv right-unit) r)
        ( is-equiv-concat' p (inv right-unit))

  equiv-con-inv :
    (p : Id x y) (q : Id y z) (r : Id x z) → Id (p ∙ q) r ≃ Id p (r ∙ (inv q))
  pr1 (equiv-con-inv p q r) = con-inv p q r
  pr2 (equiv-con-inv p q r) = is-equiv-con-inv p q r
```
