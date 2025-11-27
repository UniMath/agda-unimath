# Descent for dependent pair types

```agda
module foundation.descent-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.logical-equivalences
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.pullbacks
```

</details>

## Idea

The
{{#concept "descent property" Disambiguation="of dependent pair types" Agda=iff-descent-Σ}}
of [dependent pair types](foundation.dependent-pair-types.md) states that, given
a map `h : Y → X` and a family of maps `f : (i : I) → A i → X` together with a
family of [cones](foundation.cones-over-cospan-diagrams.md)

```text
  B i -----> Y
   |         |
   |   c i   | h
   ∨         ∨
  A i -----> X
       f i
```

for every `i`, then the family is a family of
[pullback](foundation-core.pullbacks.md) cones if and only if the total cone

```text
  Σ I B -----> Y
    |          |
    |    Σc    | h
    ∨          ∨
  Σ I A -----> X
       rec-Σ f
```

is a pullback cone.

## Theorem

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {B : I → UU l3} {X : UU l4} {Y : UU l5}
  (f : (i : I) → A i → X) (h : Y → X)
  (c : (i : I) → cone (f i) h (B i))
  where

  cone-descent-Σ : cone (rec-Σ f) h (Σ I B)
  cone-descent-Σ =
    triple
      ( tot (λ i → vertical-map-cone (f i) h (c i)))
      ( ind-Σ (λ i → horizontal-map-cone (f i) h (c i)))
      ( ind-Σ (λ i → coherence-square-cone (f i) h (c i)))

  triangle-descent-Σ :
    (i : I) (a : A i) →
    ( map-fiber-vertical-map-cone (f i) h (c i) a) ~
    ( map-fiber-vertical-map-cone (rec-Σ f) h cone-descent-Σ (i , a)) ∘
    ( map-inv-compute-fiber-tot (λ i → vertical-map-cone (f i) h (c i)) (i , a))
  triangle-descent-Σ i .(vertical-map-cone (f i) h (c i) a') (a' , refl) = refl

  abstract
    descent-Σ :
      ((i : I) → is-pullback (f i) h (c i)) →
      is-pullback (rec-Σ f) h cone-descent-Σ
    descent-Σ is-pb-c =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone
        ( rec-Σ f)
        ( h)
        ( cone-descent-Σ)
        ( ind-Σ
          ( λ i a →
            is-equiv-right-map-triangle
            ( map-fiber-vertical-map-cone (f i) h (c i) a)
            ( map-fiber-vertical-map-cone (rec-Σ f) h cone-descent-Σ (i , a))
            ( map-inv-compute-fiber-tot
              ( λ i → vertical-map-cone (f i) h (c i))
              ( i , a))
            ( triangle-descent-Σ i a)
            ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
              (f i) h (c i) (is-pb-c i) a)
            ( is-equiv-map-inv-compute-fiber-tot
              ( λ i → vertical-map-cone (f i) h (c i))
              ( i , a))))

  abstract
    descent-Σ' :
      is-pullback (rec-Σ f) h cone-descent-Σ →
      ((i : I) → is-pullback (f i) h (c i))
    descent-Σ' is-pb-dsq i =
      is-pullback-is-fiberwise-equiv-map-fiber-vertical-map-cone (f i) h (c i)
        ( λ a →
          is-equiv-left-map-triangle
          ( map-fiber-vertical-map-cone (f i) h (c i) a)
          ( map-fiber-vertical-map-cone (rec-Σ f) h cone-descent-Σ (i , a))
          ( map-inv-compute-fiber-tot
            ( λ i → vertical-map-cone (f i) h (c i))
            ( i , a))
          ( triangle-descent-Σ i a)
          ( is-equiv-map-inv-compute-fiber-tot
            ( λ i → vertical-map-cone (f i) h (c i))
            ( i , a))
          ( is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback
            ( rec-Σ f)
            ( h)
            ( cone-descent-Σ)
            ( is-pb-dsq)
            ( i , a)))

  iff-descent-Σ :
    ((i : I) → is-pullback (f i) h (c i)) ↔
    is-pullback (rec-Σ f) h cone-descent-Σ
  iff-descent-Σ = (descent-Σ , descent-Σ')
```
