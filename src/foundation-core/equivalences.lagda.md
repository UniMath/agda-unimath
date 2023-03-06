# Equivalences

```agda
{-# OPTIONS --safe #-}
```

<details><summary>Imports</summary>
```agda
module foundation-core.equivalences where
open import foundation-core.cartesian-product-types
open import foundation-core.coherently-invertible-maps
open import foundation-core.dependent-pair-types
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.universe-levels
```
</details>

## Idea

An equivalence is a map that has a section and a (separate) retraction. This is also called being biinvertible. This may look odd: Why not say that an equivalence is a map that has a 2-sided inverse? The reason is that the latter requirement would put nontrivial structure on the map, whereas having the section and retraction separate yields a property. To quickly see this: if `f` is an equivalence, then it has up to homotopy only one section, and it has up to homotopy only one retraction.

## Definition

### Equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-equiv : (A → B) → UU (l1 ⊔ l2)
  is-equiv f = sec f × retr f

_≃_ :
  {i j : Level} (A : UU i) (B : UU j) → UU (i ⊔ j)
A ≃ B = Σ (A → B) is-equiv
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

### Families of equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1}
  where

  is-fiberwise-equiv :
    {B : A → UU l2} {C : A → UU l3}
    (f : (x : A) → B x → C x) → UU (l1 ⊔ l2 ⊔ l3)
  is-fiberwise-equiv f = (x : A) → is-equiv (f x)

  fiberwise-equiv : (B : A → UU l2) (C : A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  fiberwise-equiv B C = Σ ((x : A) → B x → C x) is-fiberwise-equiv

  fam-equiv : (B : A → UU l2) (C : A → UU l3) → UU (l1 ⊔ l2 ⊔ l3)
  fam-equiv B C = (x : A) → B x ≃ C x
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

### The 3-for-2 property of equivalences

#### Composites of equivalences are equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-equiv-comp-htpy : is-equiv h → is-equiv g → is-equiv f
    pr1 (is-equiv-comp-htpy (pair sec-h retr-h) (pair sec-g retr-g)) =
      section-comp-htpy f g h H sec-h sec-g
    pr2 (is-equiv-comp-htpy (pair sec-h retr-h) (pair sec-g retr-g)) =
      retraction-comp-htpy f g h H retr-g retr-h

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-equiv-comp :
      (g : B → X) (h : A → B) → is-equiv h → is-equiv g → is-equiv (g ∘ h)
    pr1 (is-equiv-comp g h (pair sec-h retr-h) (pair sec-g retr-g)) =
      section-comp g h sec-h sec-g
    pr2 (is-equiv-comp g h (pair sec-h retr-h) (pair sec-g retr-g)) =
      retraction-comp g h retr-g retr-h

  equiv-comp : (B ≃ X) → (A ≃ B) → (A ≃ X)
  pr1 (equiv-comp g h) = (map-equiv g) ∘ (map-equiv h)
  pr2 (equiv-comp g h) = is-equiv-comp (pr1 g) (pr1 h) (pr2 h) (pr2 g)

  _∘e_ : (B ≃ X) → (A ≃ B) → (A ≃ X)
  _∘e_ = equiv-comp
```

#### If a composite and its right factor are equivalences, then so is its left factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-equiv-left-factor-htpy :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
      is-equiv f → is-equiv h → is-equiv g
    is-equiv-left-factor-htpy f g h H
      ( pair sec-f retr-f)
      ( pair (pair sh issec-sh) retr-h) =
        ( pair
          ( section-left-factor-htpy f g h H sec-f)
          ( retraction-comp-htpy g f sh
            ( triangle-section f g h H (pair sh issec-sh))
            ( retr-f)
            ( pair h issec-sh)))

  is-equiv-left-factor :
    (g : B → X) (h : A → B) →
    is-equiv (g ∘ h) → is-equiv h → is-equiv g
  is-equiv-left-factor g h is-equiv-gh is-equiv-h =
      is-equiv-left-factor-htpy (g ∘ h) g h refl-htpy is-equiv-gh is-equiv-h
```

#### If a composite and its left factor are equivalences, then so is its right factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  where

  abstract
    is-equiv-right-factor-htpy :
      (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h)) →
      is-equiv g → is-equiv f → is-equiv h
    is-equiv-right-factor-htpy f g h H
        ( pair sec-g (pair rg isretr-rg))
        ( pair sec-f retr-f) =
          ( pair
            ( section-comp-htpy h rg f
              ( triangle-retraction f g h H (pair rg isretr-rg))
              ( sec-f)
              ( pair g isretr-rg))
            ( retraction-right-factor-htpy f g h H retr-f))

  is-equiv-right-factor :
    (g : B → X) (h : A → B) →
    is-equiv g → is-equiv (g ∘ h) → is-equiv h
  is-equiv-right-factor g h is-equiv-g is-equiv-gh =
    is-equiv-right-factor-htpy (g ∘ h) g h refl-htpy is-equiv-g is-equiv-gh
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

  htpy-map-inv-is-equiv :
    {f g : A → B} (G : f ~ g) (H : is-equiv f) (K : is-equiv g) →
    (map-inv-is-equiv H) ~ (map-inv-is-equiv K)
  htpy-map-inv-is-equiv G H K b =
    ( inv
      ( isretr-map-inv-is-equiv K (map-inv-is-equiv H b))) ∙
    ( ap (map-inv-is-equiv K)
      ( ( inv (G (map-inv-is-equiv H b))) ∙
        ( issec-map-inv-is-equiv H b)))
```

### Any retraction of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-retraction :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f  → (g ∘ f) ~ id → is-equiv g
  is-equiv-is-retraction {A = A} {f = f} {g = g} is-equiv-f H =
    is-equiv-left-factor-htpy id g f (inv-htpy H) is-equiv-id is-equiv-f
```

### Any section of an equivalence is an equivalence

```agda
abstract
  is-equiv-is-section :
    {i j : Level} {A : UU i} {B : UU j} {f : A → B} {g : B → A} →
    is-equiv f → (f ∘ g) ~ id → is-equiv g
  is-equiv-is-section {B = B} {f = f} {g = g} is-equiv-f H =
    is-equiv-right-factor-htpy id f g (inv-htpy H) is-equiv-f is-equiv-id
```

### If a section of `f` is an equivalence, then `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-equiv-sec-is-equiv :
      ( sec-f : sec f) → is-equiv (pr1 sec-f) → is-equiv f
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
  is-equiv-right-factor
    ( map-equiv j)
    ( f)
    ( is-equiv-map-equiv j)
    ( is-equiv-comp-htpy
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
    ( is-equiv-comp-htpy
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
      is-equiv-right-factor-htpy (i ∘ f) g h H Eg (is-equiv-comp i f Ef Ei)

  abstract
    is-equiv-top-is-equiv-bottom-square :
      is-equiv f → is-equiv g → is-equiv i → is-equiv h
    is-equiv-top-is-equiv-bottom-square Ef Eg Ei =
      is-equiv-right-factor-htpy (i ∘ f) g h H Eg (is-equiv-comp i f Ef Ei)

  abstract
    is-equiv-bottom-is-equiv-top-square :
      is-equiv f → is-equiv g → is-equiv h → is-equiv i
    is-equiv-bottom-is-equiv-top-square Ef Eg Eh =
      is-equiv-left-factor i f (is-equiv-comp-htpy (i ∘ f) g h H Eh Eg) Ef

  abstract
    is-equiv-left-is-equiv-right-square :
      is-equiv h → is-equiv i → is-equiv g → is-equiv f
    is-equiv-left-is-equiv-right-square Eh Ei Eg =
      is-equiv-right-factor i f Ei (is-equiv-comp-htpy (i ∘ f) g h H Eh Eg)

  abstract
    is-equiv-right-is-equiv-left-square :
      is-equiv h → is-equiv i → is-equiv f → is-equiv g
    is-equiv-right-is-equiv-left-square Eh Ei Ef =
      is-equiv-left-factor-htpy (i ∘ f) g h H (is-equiv-comp i f Ef Ei) Eh
```

### Equivalences are embeddings

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-emb-is-equiv :
    {f : A → B} → is-equiv f → (x y : A) → is-equiv (ap f {x} {y})
  is-emb-is-equiv {f} H x y =
    is-equiv-has-inverse
      ( λ p →
        ( inv (isretr-map-inv-is-equiv H x)) ∙
        ( ( ap (map-inv-is-equiv H) p) ∙
          ( isretr-map-inv-is-equiv H y)))
      ( λ p →
        ( ap-concat f
          ( inv (isretr-map-inv-is-equiv H x))
          ( ap (map-inv-is-equiv H) p ∙ isretr-map-inv-is-equiv H y)) ∙
        ( ( ap-binary
            ( λ u v → u ∙ v)
            ( ap-inv f (isretr-map-inv-is-equiv H x))
            ( ( ap-concat f
                ( ap (map-inv-is-equiv H) p)
                ( isretr-map-inv-is-equiv H y)) ∙
              ( ap-binary
                ( λ u v → u ∙ v)
                ( inv (ap-comp f (map-inv-is-equiv H) p))
                ( inv (coherence-map-inv-is-equiv H y))))) ∙
          ( inv
            ( inv-con
              ( ap f (isretr-map-inv-is-equiv H x))
              ( p)
              ( ( ap (f ∘ map-inv-is-equiv H) p) ∙
                ( issec-map-inv-is-equiv H (f y)))
              ( ( ap-binary
                  ( λ u v → u ∙ v)
                  ( inv (coherence-map-inv-is-equiv H x))
                  ( inv (ap-id p))) ∙
                ( nat-htpy (issec-map-inv-is-equiv H) p))))))
      ( λ {refl → left-inv (isretr-map-inv-is-equiv H x)})

  equiv-ap :
    (e : A ≃ B) (x y : A) → (x ＝ y) ≃ (map-equiv e x ＝ map-equiv e y)
  pr1 (equiv-ap e x y) = ap (map-equiv e)
  pr2 (equiv-ap e x y) = is-emb-is-equiv (is-equiv-map-equiv e) x y
```

## See also

- For the notions of inverses and coherently invertible maps, also known as half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
