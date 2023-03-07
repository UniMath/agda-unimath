# Descent for dependent pair types

```agda
module foundation.descent-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.cones-pullbacks
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.pullbacks
open import foundation.universe-levels
```

</details>

## Theorem

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {A : I → UU l2} {A' : I → UU l3} {X : UU l4} {X' : UU l5}
  (f : (i : I) → A i → X) (h : X' → X)
  (c : (i : I) → cone (f i) h (A' i))
  where

  cone-descent-Σ : cone (ind-Σ f) h (Σ I A')
  cone-descent-Σ =
    triple
      ( tot (λ i → (pr1 (c i))))
      ( ind-Σ (λ i → (pr1 (pr2 (c i)))))
      ( ind-Σ (λ i → (pr2 (pr2 (c i)))))

  triangle-descent-Σ :
    (i : I) (a : A i) →
    ( map-fib-cone (f i) h (c i) a) ~
    ( ( map-fib-cone (ind-Σ f) h cone-descent-Σ (pair i a)) ∘
      ( map-inv-compute-fib-tot (λ i → (pr1 (c i))) (pair i a)))
  triangle-descent-Σ i .(pr1 (c i) a') (pair a' refl) = refl

  abstract
    descent-Σ :
      ((i : I) → is-pullback (f i) h (c i)) →
      is-pullback (ind-Σ f) h cone-descent-Σ
    descent-Σ is-pb-c =
      is-pullback-is-fiberwise-equiv-map-fib-cone
        ( ind-Σ f)
        ( h)
        ( cone-descent-Σ)
        ( ind-Σ
          ( λ i a → is-equiv-left-factor-htpy
            ( map-fib-cone (f i) h (c i) a)
            ( map-fib-cone (ind-Σ f) h cone-descent-Σ (pair i a))
            ( map-inv-compute-fib-tot (λ i → pr1 (c i)) (pair i a))
            ( triangle-descent-Σ i a)
            ( is-fiberwise-equiv-map-fib-cone-is-pullback
              (f i) h (c i) (is-pb-c i) a)
            ( is-equiv-map-inv-compute-fib-tot (λ i → pr1 (c i)) (pair i a))))

  abstract
    descent-Σ' :
      is-pullback (ind-Σ f) h cone-descent-Σ →
      ((i : I) → is-pullback (f i) h (c i))
    descent-Σ' is-pb-dsq i =
      is-pullback-is-fiberwise-equiv-map-fib-cone (f i) h (c i)
        ( λ a → is-equiv-comp-htpy
          ( map-fib-cone (f i) h (c i) a)
          ( map-fib-cone (ind-Σ f) h cone-descent-Σ (pair i a))
          ( map-inv-compute-fib-tot (λ i → pr1 (c i)) (pair i a))
          ( triangle-descent-Σ i a)
          ( is-equiv-map-inv-compute-fib-tot (λ i → pr1 (c i)) (pair i a))
          ( is-fiberwise-equiv-map-fib-cone-is-pullback
            ( ind-Σ f)
            ( h)
            ( cone-descent-Σ)
            ( is-pb-dsq)
            ( pair i a)))
```
