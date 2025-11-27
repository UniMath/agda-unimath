# Descent for coproduct types

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.descent-coproduct-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-fibers-of-maps
open import foundation.logical-equivalences
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
```

</details>

## Idea

The
{{#concept "descent property" Disambiguation="of coproduct types" Agda=iff-descent-coproduct}}
of [coproduct types](foundation-core.coproduct-types.md) states that given a map
`i : X' → X` and two [cones](foundation.cones-over-cospan-diagrams.md)

```text
  A' -----> X'     B' -----> X'
  |         |      |         |
  |    α    | i    |    β    | i
  ∨         ∨      ∨         ∨
  A ------> X      B ------> X
```

then the coproduct cone

```text
  A' + B' -----> X'
     |           |
     |    α+β    | i
     ∨           ∨
   A + B ------> X
```

is a [pullback](foundation-core.pullbacks.md) if and only if each cone is.

## Theorem

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3}
  {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A' → A) (g : B' → B) (i : X' → X)
  (αA : A → X) (αB : B → X) (αA' : A' → X') (αB' : B' → X')
  (HA : αA ∘ f ~ i ∘ αA') (HB : αB ∘ g ~ i ∘ αB')
  where

  triangle-descent-square-fiber-map-coproduct-inl-fiber :
    (x : A) →
    ( map-fiber-vertical-map-cone αA i (f , αA' , HA) x) ~
    ( map-fiber-vertical-map-cone (ind-coproduct _ αA αB) i
      ( map-coproduct f g , ind-coproduct _ αA' αB' , ind-coproduct _ HA HB)
      ( inl x)) ∘
    ( fiber-map-coproduct-inl-fiber f g x)
  triangle-descent-square-fiber-map-coproduct-inl-fiber x (a' , p) =
    eq-pair-eq-fiber
      ( left-whisker-concat
        ( inv (HA a'))
        ( ap-comp (ind-coproduct _ αA αB) inl p))

  triangle-descent-square-fiber-map-coproduct-inr-fiber :
    (y : B) →
    ( map-fiber-vertical-map-cone αB i (g , αB' , HB) y) ~
    ( map-fiber-vertical-map-cone (ind-coproduct _ αA αB) i
      ( map-coproduct f g , ind-coproduct _ αA' αB' , ind-coproduct _ HA HB)
      ( inr y)) ∘
    ( fiber-map-coproduct-inr-fiber f g y)
  triangle-descent-square-fiber-map-coproduct-inr-fiber y (b' , p) =
    eq-pair-eq-fiber
      ( left-whisker-concat
        ( inv (HB b'))
        ( ap-comp (ind-coproduct _ αA αB) inr p))

module _
  {l1 l2 l3 l1' l2' l3' : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {A' : UU l1'} {B' : UU l2'} {X' : UU l3'}
  (f : A → X) (g : B → X) (i : X' → X)
  (α@(h , f' , H) : cone f i A') (β@(k , g' , K) : cone g i B')
  where

  cone-descent-coproduct :
    cone (rec-coproduct f g) i (A' + B')
  pr1 (cone-descent-coproduct) = map-coproduct h k
  pr1 (pr2 cone-descent-coproduct) (inl a') = f' a'
  pr1 (pr2 cone-descent-coproduct) (inr b') = g' b'
  pr2 (pr2 cone-descent-coproduct) (inl a') = H a'
  pr2 (pr2 cone-descent-coproduct) (inr b') = K b'

  abstract
    is-fiberwise-equiv-map-fiber-vertical-map-cone-descent-coproduct :
      is-pullback f i α →
      is-pullback g i β →
      is-fiberwise-equiv
        ( map-fiber-vertical-map-cone
          ( rec-coproduct f g)
          ( i)
          ( cone-descent-coproduct))
    is-fiberwise-equiv-map-fiber-vertical-map-cone-descent-coproduct
      is-pb-α is-pb-β (inl x) =
      is-equiv-right-map-triangle
        ( map-fiber-vertical-map-cone f i (h , f' , H) x)
        ( map-fiber-vertical-map-cone (rec-coproduct f g) i
          ( cone-descent-coproduct)
          ( inl x))
        ( fiber-map-coproduct-inl-fiber h k x)
        ( triangle-descent-square-fiber-map-coproduct-inl-fiber
          h k i f g f' g' H K x)
        ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback f i
          ( h , f' , H) is-pb-α x)
        ( is-equiv-fiber-map-coproduct-inl-fiber h k x)
    is-fiberwise-equiv-map-fiber-vertical-map-cone-descent-coproduct
      is-pb-α is-pb-β (inr y) =
      is-equiv-right-map-triangle
        ( map-fiber-vertical-map-cone g i (k , g' , K) y)
        ( map-fiber-vertical-map-cone
          ( rec-coproduct f g) i
          ( cone-descent-coproduct)
          ( inr y))
        ( fiber-map-coproduct-inr-fiber h k y)
        ( triangle-descent-square-fiber-map-coproduct-inr-fiber
          h k i f g f' g' H K y)
        ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback g i
          ( k , g' , K) is-pb-β y)
        ( is-equiv-fiber-map-coproduct-inr-fiber h k y)

  abstract
    descent-coproduct :
      is-pullback f i α →
      is-pullback g i β →
      is-pullback
        ( rec-coproduct f g)
        ( i)
        ( cone-descent-coproduct)
    descent-coproduct is-pb-α is-pb-β =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
        ( rec-coproduct f g)
        ( i)
        ( cone-descent-coproduct)
        ( is-fiberwise-equiv-map-fiber-vertical-map-cone-descent-coproduct
          ( is-pb-α)
          ( is-pb-β))

  abstract
    descent-coproduct-inl :
      is-pullback
        ( rec-coproduct f g)
        ( i)
        ( cone-descent-coproduct) →
      is-pullback f i α
    descent-coproduct-inl is-pb-dsq =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone f i
        ( h , f' , H)
        ( λ a →
          is-equiv-left-map-triangle
          ( map-fiber-vertical-map-cone f i (h , f' , H) a)
          ( map-fiber-vertical-map-cone (rec-coproduct f g) i
            ( cone-descent-coproduct)
            ( inl a))
          ( fiber-map-coproduct-inl-fiber h k a)
          ( triangle-descent-square-fiber-map-coproduct-inl-fiber
            h k i f g f' g' H K a)
          ( is-equiv-fiber-map-coproduct-inl-fiber h k a)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
            ( rec-coproduct f g)
            ( i)
            ( cone-descent-coproduct)
            ( is-pb-dsq)
            ( inl a)))

  abstract
    descent-coproduct-inr :
      is-pullback
        ( rec-coproduct f g)
        ( i)
        ( cone-descent-coproduct) →
      is-pullback g i β
    descent-coproduct-inr is-pb-dsq =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone g i
        ( k , g' , K)
        ( λ b →
          is-equiv-left-map-triangle
          ( map-fiber-vertical-map-cone g i (k , g' , K) b)
          ( map-fiber-vertical-map-cone (rec-coproduct f g) i
            ( cone-descent-coproduct)
            ( inr b))
          ( fiber-map-coproduct-inr-fiber h k b)
          ( triangle-descent-square-fiber-map-coproduct-inr-fiber
            h k i f g f' g' H K b)
          ( is-equiv-fiber-map-coproduct-inr-fiber h k b)
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
            ( rec-coproduct f g)
            ( i)
            ( cone-descent-coproduct)
            ( is-pb-dsq)
            ( inr b)))

  iff-descent-coproduct :
    is-pullback f i α × is-pullback g i β ↔
    is-pullback (rec-coproduct f g) i cone-descent-coproduct
  iff-descent-coproduct =
    ( ( λ (is-pb-α , is-pb-β) → descent-coproduct is-pb-α is-pb-β) ,
      ( λ is-pb-dsq →
        ( descent-coproduct-inl is-pb-dsq , descent-coproduct-inr is-pb-dsq)))
```
