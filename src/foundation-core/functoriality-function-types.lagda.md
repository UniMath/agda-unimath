# Functoriality of function types

```agda
module foundation-core.functoriality-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality

open import foundation-core.coherently-invertible-maps
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.path-split-maps
open import foundation-core.universe-levels
```

</details>

## Properties

### A map `f` is an equivalence if and only if postcomposing by `f` is an equivalence

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  (H : {l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
  where

  map-inv-is-equiv-is-equiv-postcomp : Y → X
  map-inv-is-equiv-is-equiv-postcomp = map-inv-is-equiv (H Y) id

  issec-map-inv-is-equiv-is-equiv-postcomp :
    ( f ∘ map-inv-is-equiv-is-equiv-postcomp) ~ id
  issec-map-inv-is-equiv-is-equiv-postcomp =
    htpy-eq (issec-map-inv-is-equiv (H Y) id)

  isretr-map-inv-is-equiv-is-equiv-postcomp :
    ( map-inv-is-equiv-is-equiv-postcomp ∘ f) ~ id
  isretr-map-inv-is-equiv-is-equiv-postcomp =
    htpy-eq
      ( ap
        ( pr1)
        ( eq-is-contr
          ( is-contr-map-is-equiv (H X) f)
          { x =
            pair
              ( map-inv-is-equiv-is-equiv-postcomp ∘ f)
              ( ap (λ u → u ∘ f) (issec-map-inv-is-equiv (H Y) id))}
          { y = pair id refl}))

  abstract
    is-equiv-is-equiv-postcomp : is-equiv f
    is-equiv-is-equiv-postcomp =
      is-equiv-has-inverse
        map-inv-is-equiv-is-equiv-postcomp
        issec-map-inv-is-equiv-is-equiv-postcomp
        isretr-map-inv-is-equiv-is-equiv-postcomp
```

The following version of the same theorem works when X and Y are in the same universe. The condition of inducing equivalences by postcomposition is simplified to that universe.

```agda
is-equiv-is-equiv-postcomp' :
  {l : Level} {X : UU l} {Y : UU l} (f : X → Y) →
  ((A : UU l) → is-equiv (postcomp A f)) → is-equiv f
is-equiv-is-equiv-postcomp'
  {l} {X} {Y} f is-equiv-postcomp-f =
  let sec-f = center (is-contr-map-is-equiv (is-equiv-postcomp-f Y) id)
  in
  is-equiv-has-inverse
    ( pr1 sec-f)
    ( htpy-eq (pr2 sec-f))
    ( htpy-eq
      ( ap ( pr1)
           ( eq-is-contr'
             ( is-contr-map-is-equiv (is-equiv-postcomp-f X) f)
             ( pair ((pr1 sec-f) ∘ f) (ap (λ t → t ∘ f) (pr2 sec-f)))
             ( pair id refl))))

abstract
  is-equiv-postcomp-is-equiv :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (f : X → Y) → is-equiv f →
    ({l3 : Level} (A : UU l3) → is-equiv (postcomp A f))
  is-equiv-postcomp-is-equiv {X = X} {Y = Y} f is-equiv-f A =
    is-equiv-has-inverse
      ( postcomp A (map-inv-is-equiv is-equiv-f))
      ( λ g → eq-htpy (htpy-right-whisk (issec-map-inv-is-equiv is-equiv-f) g))
      ( λ h → eq-htpy (htpy-right-whisk (isretr-map-inv-is-equiv is-equiv-f) h))

equiv-postcomp :
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (A : UU l3) →
  (X ≃ Y) → (A → X) ≃ (A → Y)
pr1 (equiv-postcomp A e) = postcomp A (map-equiv e)
pr2 (equiv-postcomp A e) =
  is-equiv-postcomp-is-equiv (map-equiv e) (is-equiv-map-equiv e) A
```

## See also

- Functorial properties of dependent function types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).
