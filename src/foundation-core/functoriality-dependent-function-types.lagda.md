# Functoriality of dependent function types

```agda
module foundation-core.functoriality-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.families-of-equivalences
open import foundation.function-extensionality
open import foundation.implicit-function-types
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.path-split-maps
open import foundation-core.transport-along-identifications
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Properties

### The operation `map-Π` preserves homotopies

```agda
htpy-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {f f' : (i : I) → A i → B i} (H : (i : I) → (f i) ~ (f' i)) →
  map-Π f ~ map-Π f'
htpy-map-Π H h = eq-htpy (λ i → H i (h i))

htpy-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) {f f' : (i : I) → A i → B i} →
  ((i : I) → (f i) ~ (f' i)) → map-Π' α f ~ map-Π' α f'
htpy-map-Π' α H = htpy-map-Π (H ∘ α)
```

### The fibers of `map-Π`

```agda
compute-fiber-map-Π :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i) (h : (i : I) → B i) →
  ((i : I) → fiber (f i) (h i)) ≃ fiber (map-Π f) h
compute-fiber-map-Π f h =
  equiv-tot (λ _ → equiv-eq-htpy) ∘e distributive-Π-Σ

compute-fiber-map-Π' :
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  {J : UU l4} (α : J → I) (f : (i : I) → A i → B i)
  (h : (j : J) → B (α j)) →
  ((j : J) → fiber (f (α j)) (h j)) ≃ fiber (map-Π' α f) h
compute-fiber-map-Π' α f = compute-fiber-map-Π (f ∘ α)
```

### Families of equivalences induce equivalences of dependent function types

```agda
abstract
  is-equiv-map-Π-is-fiberwise-equiv :
    {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
    {f : (i : I) → A i → B i} (is-equiv-f : is-fiberwise-equiv f) →
    is-equiv (map-Π f)
  is-equiv-map-Π-is-fiberwise-equiv is-equiv-f =
    is-equiv-is-contr-map
      ( λ g →
        is-contr-equiv' _
          ( compute-fiber-map-Π _ g)
          ( is-contr-Π (λ i → is-contr-map-is-equiv (is-equiv-f i) (g i))))

equiv-Π-equiv-family :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → (A i) ≃ (B i)) → ((i : I) → A i) ≃ ((i : I) → B i)
pr1 (equiv-Π-equiv-family e) = map-Π (λ i → map-equiv (e i))
pr2 (equiv-Π-equiv-family e) =
  is-equiv-map-Π-is-fiberwise-equiv
    ( λ i → is-equiv-map-equiv (e i))
```

### Families of equivalences induce equivalences of implicit dependent function types

```agda
equiv-implicit-Π-equiv-family :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (e : (i : I) → (A i) ≃ (B i)) → ({i : I} → A i) ≃ ({i : I} → B i)
equiv-implicit-Π-equiv-family e =
  ( equiv-implicit-explicit-Π) ∘e
  ( equiv-Π-equiv-family e) ∘e
  ( equiv-explicit-implicit-Π)
```

##### Computing the inverse of `equiv-Π-equiv-family`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  compute-inv-equiv-Π-equiv-family :
    (e : (x : A) → B x ≃ C x) →
    ( map-inv-equiv (equiv-Π-equiv-family e)) ~
    ( map-equiv (equiv-Π-equiv-family λ x → (inv-equiv (e x))))
  compute-inv-equiv-Π-equiv-family e f =
    is-injective-map-equiv
      ( equiv-Π-equiv-family e)
      ( ( is-section-map-inv-equiv (equiv-Π-equiv-family e) f) ∙
        ( eq-htpy (λ x → inv (is-section-map-inv-equiv (e x) (f x)))))
```

## See also

- Arithmetical laws involving dependent function types are recorded in
  [`foundation.type-arithmetic-dependent-function-types`](foundation.type-arithmetic-dependent-function-types.md).
- Equality proofs in dependent function types are characterized in
  [`foundation.equality-dependent-function-types`](foundation.equality-dependent-function-types.md).

- Functorial properties of function types are recorded in
  [`foundation.functoriality-function-types`](foundation.functoriality-function-types.md).
- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
