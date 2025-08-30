# Functoriality of dependent pair types

```agda
module foundation-core.functoriality-dependent-pair-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.families-of-equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.retractions
open import foundation-core.retracts-of-types
open import foundation-core.sections
```

</details>

## Idea

Any map `f : A → B` and any family of maps `g : (a : A) → C a → D (f a)`
together induce a map `map-Σ D f g : Σ A C → Σ B D`. Specific instances of this
construction are also very useful: if we take `f` to be the identity map, then
we see that any family of maps `g : (a : A) → C a → D a` induces a map on total
spaces `Σ A C → Σ A D`; if we take `g` to be the family of identity maps, then
we see that for any family `D` over `B`, any map `f : A → B` induces a map
`Σ A (D ∘ f) → Σ B D`.

## Definitions

### The induced map on total spaces

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where
```

Any family of maps induces a map on the total spaces.

```agda
  tot : Σ A B → Σ A C
  tot t = (pr1 t , f (pr1 t) (pr2 t))
```

### Any map `f : A → B` induces a map `Σ A (C ∘ f) → Σ B C`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  map-Σ-map-base : Σ A (λ x → C (f x)) → Σ B C
  map-Σ-map-base s = (f (pr1 s) , pr2 s)
```

### The functorial action of dependent pair types, and its defining homotopy

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4)
  where

  map-Σ : (f : A → B) (g : (x : A) → C x → D (f x)) → Σ A C → Σ B D
  map-Σ f g t = (f (pr1 t) , g (pr1 t) (pr2 t))

  triangle-map-Σ :
    (f : A → B) (g : (x : A) → C x → D (f x)) →
    map-Σ f g ~ map-Σ-map-base f D ∘ tot g
  triangle-map-Σ f g t = refl
```

## Properties

### The map `map-Σ` preserves homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4)
  where

  htpy-map-Σ :
    {f f' : A → B} (H : f ~ f')
    (g : (x : A) → C x → D (f x)) {g' : (x : A) → C x → D (f' x)}
    (K : (x : A) → ((tr D (H x)) ∘ (g x)) ~ (g' x)) →
    (map-Σ D f g) ~ (map-Σ D f' g')
  htpy-map-Σ H g K t = eq-pair-Σ' (pair (H (pr1 t)) (K (pr1 t) (pr2 t)))
```

### The map `tot` preserves homotopies

```agda
tot-htpy :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f g : (x : A) → B x → C x} → (H : (x : A) → f x ~ g x) → tot f ~ tot g
tot-htpy H (pair x y) = eq-pair-eq-fiber (H x y)
```

### The map `tot` preserves identity maps

```agda
tot-id :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) →
  (tot (λ x (y : B x) → y)) ~ id
tot-id B p = refl
```

### The map `tot` preserves composition

```agda
preserves-comp-tot :
  {l1 l2 l3 l4 : Level}
  {A : UU l1} {B : A → UU l2} {B' : A → UU l3} {B'' : A → UU l4}
  (f : (x : A) → B x → B' x) (g : (x : A) → B' x → B'' x) →
  tot (λ x → (g x) ∘ (f x)) ~ ((tot g) ∘ (tot f))
preserves-comp-tot f g p = refl
```

### The fibers of `tot`

We show that for any family of maps, the fiber of the induced map on total
spaces are equivalent to the fibers of the maps in the family.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  (f : (x : A) → B x → C x)
  where

  map-compute-fiber-tot :
    (t : Σ A C) → fiber (tot f) t → fiber (f (pr1 t)) (pr2 t)
  pr1 (map-compute-fiber-tot .(tot f (pair x y)) (pair (pair x y) refl)) = y
  pr2 (map-compute-fiber-tot .(tot f (pair x y)) (pair (pair x y) refl)) = refl

  map-inv-compute-fiber-tot :
    (t : Σ A C) → fiber (f (pr1 t)) (pr2 t) → fiber (tot f) t
  pr1 (pr1 (map-inv-compute-fiber-tot (pair a .(f a y)) (pair y refl))) = a
  pr2 (pr1 (map-inv-compute-fiber-tot (pair a .(f a y)) (pair y refl))) = y
  pr2 (map-inv-compute-fiber-tot (pair a .(f a y)) (pair y refl)) = refl

  is-section-map-inv-compute-fiber-tot :
    (t : Σ A C) → (map-compute-fiber-tot t ∘ map-inv-compute-fiber-tot t) ~ id
  is-section-map-inv-compute-fiber-tot (pair x .(f x y)) (pair y refl) = refl

  is-retraction-map-inv-compute-fiber-tot :
    (t : Σ A C) → (map-inv-compute-fiber-tot t ∘ map-compute-fiber-tot t) ~ id
  is-retraction-map-inv-compute-fiber-tot ._ (pair (pair x y) refl) =
    refl

  abstract
    is-equiv-map-compute-fiber-tot :
      (t : Σ A C) → is-equiv (map-compute-fiber-tot t)
    is-equiv-map-compute-fiber-tot t =
      is-equiv-is-invertible
        ( map-inv-compute-fiber-tot t)
        ( is-section-map-inv-compute-fiber-tot t)
        ( is-retraction-map-inv-compute-fiber-tot t)

  compute-fiber-tot : (t : Σ A C) → fiber (tot f) t ≃ fiber (f (pr1 t)) (pr2 t)
  pr1 (compute-fiber-tot t) = map-compute-fiber-tot t
  pr2 (compute-fiber-tot t) = is-equiv-map-compute-fiber-tot t

  abstract
    is-equiv-map-inv-compute-fiber-tot :
      (t : Σ A C) → is-equiv (map-inv-compute-fiber-tot t)
    is-equiv-map-inv-compute-fiber-tot t =
      is-equiv-is-invertible
        ( map-compute-fiber-tot t)
        ( is-retraction-map-inv-compute-fiber-tot t)
        ( is-section-map-inv-compute-fiber-tot t)

  inv-compute-fiber-tot :
    (t : Σ A C) → fiber (f (pr1 t)) (pr2 t) ≃ fiber (tot f) t
  pr1 (inv-compute-fiber-tot t) = map-inv-compute-fiber-tot t
  pr2 (inv-compute-fiber-tot t) = is-equiv-map-inv-compute-fiber-tot t
```

### A family of maps `f` is a family of equivalences if and only if `tot f` is an equivalence

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f : (x : A) → B x → C x}
  where

  abstract
    is-equiv-tot-is-fiberwise-equiv : is-fiberwise-equiv f → is-equiv (tot f)
    is-equiv-tot-is-fiberwise-equiv H =
      is-equiv-is-contr-map
        ( λ t →
          is-contr-is-equiv
            ( fiber (f (pr1 t)) (pr2 t))
            ( map-compute-fiber-tot f t)
            ( is-equiv-map-compute-fiber-tot f t)
            ( is-contr-map-is-equiv (H (pr1 t)) (pr2 t)))

  abstract
    is-fiberwise-equiv-is-equiv-tot : is-equiv (tot f) → is-fiberwise-equiv f
    is-fiberwise-equiv-is-equiv-tot is-equiv-tot-f x =
      is-equiv-is-contr-map
        ( λ z →
          is-contr-is-equiv'
            ( fiber (tot f) (pair x z))
            ( map-compute-fiber-tot f (pair x z))
            ( is-equiv-map-compute-fiber-tot f (pair x z))
            ( is-contr-map-is-equiv is-equiv-tot-f (pair x z)))
```

### The action of `tot` on equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  equiv-tot : ((x : A) → B x ≃ C x) → (Σ A B) ≃ (Σ A C)
  pr1 (equiv-tot e) = tot (λ x → map-equiv (e x))
  pr2 (equiv-tot e) =
    is-equiv-tot-is-fiberwise-equiv (λ x → is-equiv-map-equiv (e x))
```

### The action of `tot` on retracts

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  where

  retraction-tot :
    {f : (x : A) → B x → C x} →
    ((x : A) → retraction (f x)) → retraction (tot f)
  pr1 (retraction-tot {f} r) (x , z) =
    ( x , map-retraction (f x) (r x) z)
  pr2 (retraction-tot {f} r) (x , z) =
    eq-pair-eq-fiber (is-retraction-map-retraction (f x) (r x) z)

  retract-tot : ((x : A) → (B x) retract-of (C x)) → (Σ A B) retract-of (Σ A C)
  pr1 (retract-tot r) = tot (λ x → inclusion-retract (r x))
  pr2 (retract-tot r) = retraction-tot (λ x → retraction-retract (r x))
```

### The fibers of `map-Σ-map-base`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  fiber-map-Σ-map-base-fiber :
    (t : Σ B C) → fiber f (pr1 t) → fiber (map-Σ-map-base f C) t
  pr1 (pr1 (fiber-map-Σ-map-base-fiber (pair .(f x) z) (pair x refl))) = x
  pr2 (pr1 (fiber-map-Σ-map-base-fiber (pair .(f x) z) (pair x refl))) = z
  pr2 (fiber-map-Σ-map-base-fiber (pair .(f x) z) (pair x refl)) = refl

  fiber-fiber-map-Σ-map-base :
    (t : Σ B C) → fiber (map-Σ-map-base f C) t → fiber f (pr1 t)
  pr1
    ( fiber-fiber-map-Σ-map-base
      .(map-Σ-map-base f C (pair x z)) (pair (pair x z) refl)) = x
  pr2
    ( fiber-fiber-map-Σ-map-base
      .(map-Σ-map-base f C (pair x z)) (pair (pair x z) refl)) = refl

  is-section-fiber-fiber-map-Σ-map-base :
    (t : Σ B C) →
    (fiber-map-Σ-map-base-fiber t ∘ fiber-fiber-map-Σ-map-base t) ~ id
  is-section-fiber-fiber-map-Σ-map-base .(pair (f x) z) (pair (pair x z) refl) =
    refl

  is-retraction-fiber-fiber-map-Σ-map-base :
    (t : Σ B C) →
    (fiber-fiber-map-Σ-map-base t ∘ fiber-map-Σ-map-base-fiber t) ~ id
  is-retraction-fiber-fiber-map-Σ-map-base (pair .(f x) z) (pair x refl) = refl

  abstract
    is-equiv-fiber-map-Σ-map-base-fiber :
      (t : Σ B C) → is-equiv (fiber-map-Σ-map-base-fiber t)
    is-equiv-fiber-map-Σ-map-base-fiber t =
      is-equiv-is-invertible
        ( fiber-fiber-map-Σ-map-base t)
        ( is-section-fiber-fiber-map-Σ-map-base t)
        ( is-retraction-fiber-fiber-map-Σ-map-base t)

  compute-fiber-map-Σ-map-base :
    (t : Σ B C) → fiber f (pr1 t) ≃ fiber (map-Σ-map-base f C) t
  pr1 (compute-fiber-map-Σ-map-base t) = fiber-map-Σ-map-base-fiber t
  pr2 (compute-fiber-map-Σ-map-base t) =
    is-equiv-fiber-map-Σ-map-base-fiber t
```

### The fibers of `map-Σ`

We compute the fibers of `map-Σ` first in terms of `fiber'` and then in terms of
`fiber`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3} (D : B → UU l4)
  (f : A → B) (g : (x : A) → C x → D (f x)) (t : Σ B D)
  where

  fiber-map-Σ' : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiber-map-Σ' =
    Σ (fiber' f (pr1 t)) (λ s → fiber' (g (pr1 s)) (tr D (pr2 s) (pr2 t)))

  map-fiber-map-Σ' : fiber' (map-Σ D f g) t → fiber-map-Σ'
  map-fiber-map-Σ' ((a , c) , refl) = (a , refl) , (c , refl)

  map-inv-fiber-map-Σ' : fiber-map-Σ' → fiber' (map-Σ D f g) t
  map-inv-fiber-map-Σ' ((a , p) , (c , q)) = ((a , c) , eq-pair-Σ p q)

  abstract
    is-section-map-inv-fiber-map-Σ' :
      is-section map-fiber-map-Σ' map-inv-fiber-map-Σ'
    is-section-map-inv-fiber-map-Σ' ((a , refl) , (c , refl)) = refl

  abstract
    is-retraction-map-inv-fiber-map-Σ' :
      is-retraction map-fiber-map-Σ' map-inv-fiber-map-Σ'
    is-retraction-map-inv-fiber-map-Σ' ((a , c) , refl) = refl

  is-equiv-map-fiber-map-Σ' : is-equiv map-fiber-map-Σ'
  is-equiv-map-fiber-map-Σ' =
    is-equiv-is-invertible
      map-inv-fiber-map-Σ'
      is-section-map-inv-fiber-map-Σ'
      is-retraction-map-inv-fiber-map-Σ'

  compute-fiber-map-Σ' : fiber' (map-Σ D f g) t ≃ fiber-map-Σ'
  compute-fiber-map-Σ' = (map-fiber-map-Σ' , is-equiv-map-fiber-map-Σ')

  fiber-map-Σ : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  fiber-map-Σ =
    Σ (fiber f (pr1 t)) (λ s → fiber (g (pr1 s)) (inv-tr D (pr2 s) (pr2 t)))

  map-fiber-map-Σ : fiber (map-Σ D f g) t → fiber-map-Σ
  map-fiber-map-Σ ((a , c) , refl) = (a , refl) , (c , refl)

  map-inv-fiber-map-Σ : fiber-map-Σ → fiber (map-Σ D f g) t
  map-inv-fiber-map-Σ ((a , refl) , c , refl) = ((a , c) , refl)

  abstract
    is-section-map-inv-fiber-map-Σ :
      is-section map-fiber-map-Σ map-inv-fiber-map-Σ
    is-section-map-inv-fiber-map-Σ ((a , refl) , (c , refl)) = refl

  abstract
    is-retraction-map-inv-fiber-map-Σ :
      is-retraction map-fiber-map-Σ map-inv-fiber-map-Σ
    is-retraction-map-inv-fiber-map-Σ ((a , c) , refl) = refl

  is-equiv-map-fiber-map-Σ : is-equiv map-fiber-map-Σ
  is-equiv-map-fiber-map-Σ =
    is-equiv-is-invertible
      map-inv-fiber-map-Σ
      is-section-map-inv-fiber-map-Σ
      is-retraction-map-inv-fiber-map-Σ

  compute-fiber-map-Σ : fiber (map-Σ D f g) t ≃ fiber-map-Σ
  compute-fiber-map-Σ = (map-fiber-map-Σ , is-equiv-map-fiber-map-Σ)
```

### If `f : A → B` is a contractible map, then so is `map-Σ-map-base f C`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  abstract
    is-contr-map-map-Σ-map-base :
      is-contr-map f → is-contr-map (map-Σ-map-base f C)
    is-contr-map-map-Σ-map-base is-contr-f (pair y z) =
      is-contr-equiv'
        ( fiber f y)
        ( compute-fiber-map-Σ-map-base f C (pair y z))
        ( is-contr-f y)
```

### If `f : A → B` is an equivalence, then so is `map-Σ-map-base f C`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (C : B → UU l3)
  where

  abstract
    is-equiv-map-Σ-map-base : is-equiv f → is-equiv (map-Σ-map-base f C)
    is-equiv-map-Σ-map-base is-equiv-f =
      is-equiv-is-contr-map
        ( is-contr-map-map-Σ-map-base f C (is-contr-map-is-equiv is-equiv-f))

equiv-Σ-equiv-base :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : B → UU l3) (e : A ≃ B) →
  Σ A (C ∘ map-equiv e) ≃ Σ B C
pr1 (equiv-Σ-equiv-base C (pair f is-equiv-f)) =
  map-Σ-map-base f C
pr2 (equiv-Σ-equiv-base C (pair f is-equiv-f)) =
  is-equiv-map-Σ-map-base f C is-equiv-f
```

### The functorial action of dependent pair types preserves equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : A → UU l3}
  (D : B → UU l4)
  where

  abstract
    is-equiv-map-Σ :
      {f : A → B} {g : (x : A) → C x → D (f x)} →
      is-equiv f → is-fiberwise-equiv g → is-equiv (map-Σ D f g)
    is-equiv-map-Σ {f} {g} is-equiv-f is-fiberwise-equiv-g =
      is-equiv-left-map-triangle
        ( map-Σ D f g)
        ( map-Σ-map-base f D)
        ( tot g)
        ( triangle-map-Σ D f g)
        ( is-equiv-tot-is-fiberwise-equiv is-fiberwise-equiv-g)
        ( is-equiv-map-Σ-map-base f D is-equiv-f)

  equiv-Σ :
    (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) → Σ A C ≃ Σ B D
  pr1 (equiv-Σ e g) = map-Σ D (map-equiv e) (λ x → map-equiv (g x))
  pr2 (equiv-Σ e g) =
    is-equiv-map-Σ
      ( is-equiv-map-equiv e)
      ( λ x → is-equiv-map-equiv (g x))

  abstract
    is-fiberwise-equiv-is-equiv-map-Σ :
      (f : A → B) (g : (x : A) → C x → D (f x)) →
      is-equiv f → is-equiv (map-Σ D f g) → is-fiberwise-equiv g
    is-fiberwise-equiv-is-equiv-map-Σ f g H K =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-map-triangle
          ( map-Σ D f g)
          ( map-Σ-map-base f D)
          ( tot g)
          ( triangle-map-Σ D f g)
          ( is-equiv-map-Σ-map-base f D H)
          ( K))

  map-equiv-Σ :
    (e : A ≃ B) (g : (x : A) → C x ≃ D (map-equiv e x)) → Σ A C → Σ B D
  map-equiv-Σ e g = map-equiv (equiv-Σ e g)
```

### Any commuting triangle induces a map on fibers

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  where

  fiber-triangle :
    (x : X) → fiber f x → fiber g x
  pr1 (fiber-triangle .(f a) (a , refl)) = h a
  pr2 (fiber-triangle .(f a) (a , refl)) = inv (H a)

  square-tot-fiber-triangle :
    ( h ∘ map-equiv-total-fiber f) ~
    ( map-equiv-total-fiber g ∘ tot fiber-triangle)
  square-tot-fiber-triangle (.(f a) , a , refl) = refl
```

### In a commuting triangle, the top map is an equivalence if and only if it induces an equivalence on fibers

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {A : UU l2} {B : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ (g ∘ h))
  where

  abstract
    is-fiberwise-equiv-is-equiv-triangle :
      is-equiv h → is-fiberwise-equiv (fiber-triangle f g h H)
    is-fiberwise-equiv-is-equiv-triangle E =
      is-fiberwise-equiv-is-equiv-tot
        ( is-equiv-top-is-equiv-bottom-square
          ( map-equiv-total-fiber f)
          ( map-equiv-total-fiber g)
          ( tot (fiber-triangle f g h H))
          ( h)
          ( square-tot-fiber-triangle f g h H)
          ( is-equiv-map-equiv-total-fiber f)
          ( is-equiv-map-equiv-total-fiber g)
          ( E))

  abstract
    is-equiv-triangle-is-fiberwise-equiv :
      is-fiberwise-equiv (fiber-triangle f g h H) → is-equiv h
    is-equiv-triangle-is-fiberwise-equiv E =
      is-equiv-bottom-is-equiv-top-square
        ( map-equiv-total-fiber f)
        ( map-equiv-total-fiber g)
        ( tot (fiber-triangle f g h H))
        ( h)
        ( square-tot-fiber-triangle f g h H)
        ( is-equiv-map-equiv-total-fiber f)
        ( is-equiv-map-equiv-total-fiber g)
        ( is-equiv-tot-is-fiberwise-equiv E)
```

### `map-Σ` preserves identity maps

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  compute-map-Σ-id : map-Σ B id (λ _ → id) ~ id
  compute-map-Σ-id = refl-htpy
```

### `map-Σ` preserves composition of maps

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  {A' : A → UU l4} {B' : B → UU l5} {C' : C → UU l6}
  {f : A → B} {f' : (x : A) → A' x → B' (f x)}
  {g : B → C} {g' : (y : B) → B' y → C' (g y)}
  where

  preserves-comp-map-Σ :
    map-Σ C' (g ∘ f) (λ x x' → g' (f x) (f' x x')) ~
    map-Σ C' g g' ∘ map-Σ B' f f'
  preserves-comp-map-Σ = refl-htpy
```

### Computing the action on identifications of `tot`

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {X : A → UU l2} {Y : A → UU l3}
  (g : (a : A) → X a → Y a) {a a' : A} {x : X a} {x' : X a'}
  where

  coh-ap-tot :
    pair-eq-Σ ∘ ap (tot g) {a , x} {a' , x'} ~
    tot (λ p q → inv-preserves-tr g p x ∙ ap (g a') q) ∘ pair-eq-Σ
  coh-ap-tot refl = refl

  compute-ap-tot :
    (p : a ＝ a') →
    (q : dependent-identification X p x x') →
    ap (tot g) {a , x} {a' , x'} (eq-pair-Σ p q) ＝
    eq-pair-Σ p (inv-preserves-tr g p x ∙ ap (g a') q)
  compute-ap-tot refl refl = refl

  compute-ap-tot' :
    (p : (a , x) ＝ (a' , x')) →
    ap (tot g) {a , x} {a' , x'} p ＝
    eq-pair-Σ
      ( ap pr1 p)
      ( inv-preserves-tr g (ap pr1 p) x ∙
        ap (g a') (tr-ap pr1 (λ x _ → pr2 x) p a))
  compute-ap-tot' refl = refl

  inv-compute-ap-tot' :
    (p : (a , x) ＝ (a' , x')) →
    eq-pair-Σ
      ( ap pr1 p)
      ( inv-preserves-tr g (ap pr1 p) x ∙
        ap (g a') (tr-ap pr1 (λ x _ → pr2 x) p a)) ＝
    ap (tot g) {a , x} {a' , x'} p
  inv-compute-ap-tot' p = inv (compute-ap-tot' p)

```

### Computing the action on identifications of the functorial action of Σ

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : A → UU l3} (Y : B → UU l4)
  (f : A → B) (g : (a : A) → X a → Y (f a)) {a a' : A} {x : X a} {x' : X a'}
  where

  compute-ap-map-Σ :
    pair-eq-Σ ∘ ap (map-Σ Y f g) ~
    map-Σ
      ( λ p → dependent-identification Y p (g a x) (g a' x'))
      ( ap f {a} {a'})
      ( λ p q → tr-ap f g p x ∙ ap (g a') q) ∘
    pair-eq-Σ
  compute-ap-map-Σ refl = refl
```

## See also

- Arithmetical laws involving dependent pair types are recorded in
  [`foundation.type-arithmetic-dependent-pair-types`](foundation.type-arithmetic-dependent-pair-types.md).
- Equality proofs in dependent pair types are characterized in
  [`foundation.equality-dependent-pair-types`](foundation.equality-dependent-pair-types.md).
- The universal property of dependent pair types is treated in
  [`foundation.universal-property-dependent-pair-types`](foundation.universal-property-dependent-pair-types.md).
- Functorial properties of cartesian product types are recorded in
  [`foundation.functoriality-cartesian-product-types`](foundation.functoriality-cartesian-product-types.md).
- Functorial properties of dependent product types are recorded in
  [`foundation.functoriality-dependent-function-types`](foundation.functoriality-dependent-function-types.md).
