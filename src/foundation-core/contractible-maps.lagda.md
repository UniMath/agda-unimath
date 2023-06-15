# Contractible maps

```agda
module foundation-core.contractible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.coherently-invertible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

A map is often said to satisfy a property `P` if each of its fibers satisfy
property `P`. Thus, we define contractible maps to be maps of which each fiber
is contractible. In other words, contractible maps are maps `f : A → B` such
that for each element `b : B` there is a unique `a : A` equipped with an
identification `(f a) ＝ b`, i.e., contractible maps are the type theoretic
bijections.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-map : (A → B) → UU (l1 ⊔ l2)
  is-contr-map f = (y : B) → is-contr (fib f y)
```

## Properties

### Any contractible map is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  map-inv-is-contr-map : is-contr-map f → B → A
  map-inv-is-contr-map H y = pr1 (center (H y))

  is-section-map-inv-is-contr-map :
    (H : is-contr-map f) → (f ∘ (map-inv-is-contr-map H)) ~ id
  is-section-map-inv-is-contr-map H y = pr2 (center (H y))

  is-retraction-map-inv-is-contr-map :
    (H : is-contr-map f) → ((map-inv-is-contr-map H) ∘ f) ~ id
  is-retraction-map-inv-is-contr-map H x =
    ap
      ( pr1 {B = λ z → (f z) ＝ (f x)})
      ( ( inv
          ( contraction
            ( H (f x))
            ( pair
              ( map-inv-is-contr-map H (f x))
              ( is-section-map-inv-is-contr-map H (f x))))) ∙
        ( contraction (H (f x)) (pair x refl)))

  abstract
    is-equiv-is-contr-map : is-contr-map f → is-equiv f
    is-equiv-is-contr-map H =
      is-equiv-has-inverse
        ( map-inv-is-contr-map H)
        ( is-section-map-inv-is-contr-map H)
        ( is-retraction-map-inv-is-contr-map H)
```

### Any coherently invertible map is a contractible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    center-fib-is-coherently-invertible :
      is-coherently-invertible f → (y : B) → fib f y
    pr1 (center-fib-is-coherently-invertible H y) =
      inv-is-coherently-invertible H y
    pr2 (center-fib-is-coherently-invertible H y) =
      is-section-inv-is-coherently-invertible H y

    contraction-fib-is-coherently-invertible :
      (H : is-coherently-invertible f) → (y : B) → (t : fib f y) →
      (center-fib-is-coherently-invertible H y) ＝ t
    contraction-fib-is-coherently-invertible H y (pair x refl) =
      eq-Eq-fib f y
        ( is-retraction-inv-is-coherently-invertible H x)
        ( ( right-unit) ∙
          ( inv ( coh-inv-is-coherently-invertible H x)))

  is-contr-map-is-coherently-invertible :
    is-coherently-invertible f → is-contr-map f
  pr1 (is-contr-map-is-coherently-invertible H y) =
    center-fib-is-coherently-invertible H y
  pr2 (is-contr-map-is-coherently-invertible H y) =
    contraction-fib-is-coherently-invertible H y
```

### Any equivalence is a contractible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-contr-map-is-equiv : is-equiv f → is-contr-map f
    is-contr-map-is-equiv =
      is-contr-map-is-coherently-invertible ∘ is-coherently-invertible-is-equiv
```

## See also

- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notions of inverses and coherently invertible maps, also known as
  half-adjoint equivalences, see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
