# Equality in the fibers of a map

```agda
module foundation.equality-fibers-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
```

</details>

## Idea

In the file
[`foundation-core.fibers-of-maps`](foundation-core.fibers-of-maps.md) we already
gave one characterization of the identity type of `fiber f b`, for an arbitrary
map `f : A → B`. Here we give a second characterization, using the fibers of the
action on identifications of `f`.

## Theorem

For any map `f : A → B` any `b : B` and any `x y : fiber f b`, there is an
equivalence

```text
(x ＝ y) ≃ fiber (ap f) ((pr2 x) ∙ (inv (pr2 y)))
```

### Proof

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {b : B}
  where

  fiber-ap-eq-fiber-fiberwise :
    (s t : fiber f b) (p : (pr1 s) ＝ (pr1 t)) →
    ((tr (λ (a : A) → (f a) ＝ b) p (pr2 s)) ＝ (pr2 t)) →
    (ap f p ＝ ((pr2 s) ∙ (inv (pr2 t))))
  fiber-ap-eq-fiber-fiberwise (pair .x' p) (pair x' refl) refl =
    inv ∘ (concat right-unit refl)

  abstract
    is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwise :
      (s t : fiber f b) → is-fiberwise-equiv (fiber-ap-eq-fiber-fiberwise s t)
    is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwise
      ( pair x y)
      ( pair .x refl)
      ( refl) =
      is-equiv-comp
        ( inv)
        ( concat right-unit refl)
        ( is-equiv-concat right-unit refl)
        ( is-equiv-inv (y ∙ refl) refl)

  fiber-ap-eq-fiber :
    (s t : fiber f b) → s ＝ t →
    fiber (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
  pr1 (fiber-ap-eq-fiber s .s refl) = refl
  pr2 (fiber-ap-eq-fiber s .s refl) = inv (right-inv (pr2 s))

  triangle-fiber-ap-eq-fiber :
    (s t : fiber f b) →
    ( fiber-ap-eq-fiber s t) ~
    ( (tot (fiber-ap-eq-fiber-fiberwise s t)) ∘ (pair-eq-Σ {s = s} {t}))
  triangle-fiber-ap-eq-fiber (pair x refl) .(pair x refl) refl = refl

  abstract
    is-equiv-fiber-ap-eq-fiber :
      (s t : fiber f b) → is-equiv (fiber-ap-eq-fiber s t)
    is-equiv-fiber-ap-eq-fiber s t =
      is-equiv-comp-htpy
        ( fiber-ap-eq-fiber s t)
        ( tot (fiber-ap-eq-fiber-fiberwise s t))
        ( pair-eq-Σ {s = s} {t})
        ( triangle-fiber-ap-eq-fiber s t)
        ( is-equiv-pair-eq-Σ s t)
        ( is-equiv-tot-is-fiberwise-equiv
          ( is-fiberwise-equiv-fiber-ap-eq-fiber-fiberwise s t))

  equiv-fiber-ap-eq-fiber :
    (s t : fiber f b) →
    (s ＝ t) ≃ fiber (ap f {x = pr1 s} {y = pr1 t}) ((pr2 s) ∙ (inv (pr2 t)))
  pr1 (equiv-fiber-ap-eq-fiber s t) = fiber-ap-eq-fiber s t
  pr2 (equiv-fiber-ap-eq-fiber s t) = is-equiv-fiber-ap-eq-fiber s t

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x y : A)
  where

  eq-fiber-fiber-ap :
    (q : f x ＝ f y) → (pair x q) ＝ (pair y refl) → fiber (ap f {x} {y}) q
  eq-fiber-fiber-ap q =
    ( tr (fiber (ap f)) right-unit) ∘
    ( fiber-ap-eq-fiber f (pair x q) (pair y refl))

  abstract
    is-equiv-eq-fiber-fiber-ap :
      (q : (f x) ＝ (f y)) → is-equiv (eq-fiber-fiber-ap q)
    is-equiv-eq-fiber-fiber-ap q =
      is-equiv-comp
        ( tr (fiber (ap f)) right-unit)
        ( fiber-ap-eq-fiber f (pair x q) (pair y refl))
        ( is-equiv-fiber-ap-eq-fiber f (pair x q) (pair y refl))
        ( is-equiv-tr (fiber (ap f)) right-unit)
```

## See also

- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
