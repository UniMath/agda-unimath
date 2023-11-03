# Functoriality of cartesian product types

```agda
module foundation.functoriality-cartesian-product-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

Any two maps `f : A → B` and `g : C → D` induce a map
`map-prod : A × B → C × D`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D)
  where

  map-prod : A × B → C × D
  pr1 (map-prod t) = f (pr1 t)
  pr2 (map-prod t) = g (pr2 t)

  map-prod-pr1 : pr1 ∘ map-prod ~ f ∘ pr1
  map-prod-pr1 (a , b) = refl

  map-prod-pr2 : pr2 ∘ map-prod ~ g ∘ pr2
  map-prod-pr2 (a , b) = refl
```

## Properties

### Functoriality of products preserves identity maps

```agda
map-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  map-prod (id {A = A}) (id {A = B}) ~ id
map-prod-id (a , b) = refl
```

### Functoriality of products preserves composition

```agda
map-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-prod (h ∘ f) (k ∘ g) ~ map-prod h k ∘ map-prod f g
map-prod-comp f g h k t = refl
```

### Functoriality of products preserves homotopies

```agda
htpy-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-prod f g ~ map-prod f' g'
htpy-map-prod H K (a , b) = eq-pair (H a) (K b)
```

### Functoriality of products preserves equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  map-inv-map-prod :
    (f : A → C) (g : B → D) → is-equiv f → is-equiv g → C × D → A × B
  pr1 (map-inv-map-prod f g H K (c , d)) = map-inv-is-equiv H c
  pr2 (map-inv-map-prod f g H K (c , d)) = map-inv-is-equiv K d

  is-section-map-inv-map-prod :
    (f : A → C) (g : B → D) (H : is-equiv f) (K : is-equiv g) →
    map-prod f g ∘ map-inv-map-prod f g H K ~ id
  is-section-map-inv-map-prod f g H K =
    htpy-map-prod
      ( is-section-map-inv-is-equiv H)
      ( is-section-map-inv-is-equiv K)

  is-retraction-map-inv-map-prod :
    (f : A → C) (g : B → D) (H : is-equiv f) (K : is-equiv g) →
    map-inv-map-prod f g H K ∘ map-prod f g ~ id
  is-retraction-map-inv-map-prod f g H K =
    htpy-map-prod
      ( is-retraction-map-inv-is-equiv H)
      ( is-retraction-map-inv-is-equiv K)

  is-equiv-map-prod :
    (f : A → C) (g : B → D) →
    is-equiv f → is-equiv g → is-equiv (map-prod f g)
  is-equiv-map-prod f g H K =
    is-equiv-is-invertible
      ( map-inv-map-prod f g H K)
      ( is-section-map-inv-map-prod f g H K)
      ( is-retraction-map-inv-map-prod f g H K)

  equiv-prod : A ≃ C → B ≃ D → A × B ≃ C × D
  pr1 (equiv-prod (f , is-equiv-f) (g , is-equiv-g)) = map-prod f g
  pr2 (equiv-prod (f , is-equiv-f) (g , is-equiv-g)) =
    is-equiv-map-prod f g is-equiv-f is-equiv-g
```

### Functoriality of products preserves equivalences in either factor

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  equiv-prod-left : A ≃ C → A × B ≃ C × B
  equiv-prod-left f = equiv-prod f id-equiv

  equiv-prod-right : B ≃ C → A × B ≃ A × C
  equiv-prod-right = equiv-prod id-equiv
```

### The fibers of `map-prod f g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D) (t : C × D)
  where

  map-compute-fiber-map-prod :
    fiber (map-prod f g) t → fiber f (pr1 t) × fiber g (pr2 t)
  pr1 (pr1 (map-compute-fiber-map-prod ((a , b) , refl))) = a
  pr2 (pr1 (map-compute-fiber-map-prod ((a , b) , refl))) = refl
  pr1 (pr2 (map-compute-fiber-map-prod ((a , b) , refl))) = b
  pr2 (pr2 (map-compute-fiber-map-prod ((a , b) , refl))) = refl

  map-inv-compute-fiber-map-prod :
    fiber f (pr1 t) × fiber g (pr2 t) → fiber (map-prod f g) t
  pr1 (pr1 (map-inv-compute-fiber-map-prod ((x , refl) , (y , refl)))) = x
  pr2 (pr1 (map-inv-compute-fiber-map-prod ((x , refl) , (y , refl)))) = y
  pr2 (map-inv-compute-fiber-map-prod ((x , refl) , (y , refl))) = refl

  is-section-map-inv-compute-fiber-map-prod :
    map-compute-fiber-map-prod ∘ map-inv-compute-fiber-map-prod ~ id
  is-section-map-inv-compute-fiber-map-prod ((x , refl) , (y , refl)) = refl

  is-retraction-map-inv-compute-fiber-map-prod :
    map-inv-compute-fiber-map-prod ∘ map-compute-fiber-map-prod ~ id
  is-retraction-map-inv-compute-fiber-map-prod ((a , b) , refl) = refl

  is-equiv-map-compute-fiber-map-prod : is-equiv map-compute-fiber-map-prod
  is-equiv-map-compute-fiber-map-prod =
    is-equiv-is-invertible
      ( map-inv-compute-fiber-map-prod)
      ( is-section-map-inv-compute-fiber-map-prod)
      ( is-retraction-map-inv-compute-fiber-map-prod)

  compute-fiber-map-prod :
    fiber (map-prod f g) t ≃ (fiber f (pr1 t) × fiber g (pr2 t))
  pr1 compute-fiber-map-prod = map-compute-fiber-map-prod
  pr2 compute-fiber-map-prod = is-equiv-map-compute-fiber-map-prod
```

### If `map-prod f g : A × B → C × D` is an equivalence, then we have `D → is-equiv f` and `C → is-equiv g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D)
  where

  is-equiv-left-factor-is-equiv-map-prod :
    (d : D) → is-equiv (map-prod f g) → is-equiv f
  is-equiv-left-factor-is-equiv-map-prod d is-equiv-fg =
    is-equiv-is-contr-map
      ( λ x →
        is-contr-left-factor-prod
          ( fiber f x)
          ( fiber g d)
          ( is-contr-is-equiv'
            ( fiber (map-prod f g) (x , d))
            ( map-compute-fiber-map-prod f g (x , d))
            ( is-equiv-map-compute-fiber-map-prod f g (x , d))
            ( is-contr-map-is-equiv is-equiv-fg (x , d))))

  is-equiv-right-factor-is-equiv-map-prod :
    (c : C) → is-equiv (map-prod f g) → is-equiv g
  is-equiv-right-factor-is-equiv-map-prod c is-equiv-fg =
    is-equiv-is-contr-map
      ( λ y →
        is-contr-right-factor-prod
          ( fiber f c)
          ( fiber g y)
          ( is-contr-is-equiv'
            ( fiber (map-prod f g) (c , y))
            ( map-compute-fiber-map-prod f g (c , y))
            ( is-equiv-map-compute-fiber-map-prod f g (c , y))
            ( is-contr-map-is-equiv is-equiv-fg (c , y))))
```

## See also

- Arithmetical laws involving cartesian product types are recorded in
  [`foundation.type-arithmetic-cartesian-product-types`](foundation.type-arithmetic-cartesian-product-types.md).
- Equality proofs in cartesian product types are characterized in
  [`foundation.equality-cartesian-product-types`](foundation.equality-cartesian-product-types.md).
- The universal property of cartesian product types is treated in
  [`foundation.universal-property-cartesian-product-types`](foundation.universal-property-cartesian-product-types.md).

- Functorial properties of dependent pair types are recorded in
  [`foundation.functoriality-dependent-pair-types`](foundation.functoriality-dependent-pair-types.md).
- Functorial properties of dependent product types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
- Functorial properties of coproduct types are recorded in
  [`foundation.functoriality-coproduct-types`](foundation.functoriality-coproduct-types.md).
