#  Functoriality of cartesian product types

```agda
module foundation.functoriality-cartesian-product-types where

open import foundation-core.cartesian-product-types
open import foundation-core.constant-maps
open import foundation-core.coherently-invertible-maps
open import foundation-core.dependent-pair-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.universe-levels
open import foundation-core.sections
open import foundation-core.retractions
```

## Idea

Any two maps `f : A → B` and `g : C → D` induce a map `map-prod : A × B → C × D`.

## Definition

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  map-prod : (f : A → C) (g : B → D) → (A × B) → (C × D)
  pr1 (map-prod f g t) = f (pr1 t)
  pr2 (map-prod f g t) = g (pr2 t)

  map-prod-pr1 :
    (f : A → C) (g : B → D) → (pr1 ∘ (map-prod f g)) ~ (f ∘ pr1)
  map-prod-pr1 f g (pair a b) = refl

  map-prod-pr2 :
    (f : A → C) (g : B → D) → (pr2 ∘ (map-prod f g)) ~ (g ∘ pr2)
  map-prod-pr2 f g (pair a b) = refl
```

## Properties

### Functoriality of products preserves identity maps

```agda
map-prod-id :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (map-prod (id {A = A}) (id {A = B})) ~ id
map-prod-id (pair a b) = refl
```

### Functoriality of products preserves composition

```agda
map-prod-comp :
  {l1 l2 l3 l4 l5 l6 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {E : UU l5} {F : UU l6} (f : A → C) (g : B → D) (h : C → E) (k : D → F) →
  map-prod (h ∘ f) (k ∘ g) ~ ((map-prod h k) ∘ (map-prod f g))
map-prod-comp f g h k t = refl
```

### Functoriality of products preserves homotopies

```agda
htpy-map-prod :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  {f f' : A → C} (H : f ~ f') {g g' : B → D} (K : g ~ g') →
  map-prod f g ~ map-prod f' g'
htpy-map-prod {f = f} {f'} H {g} {g'} K (pair a b) =
  eq-pair (H a) (K b)
```

### Functoriality of products preserves equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  where

  abstract
    is-equiv-map-prod :
      (f : A → C) (g : B → D) →
      is-equiv f → is-equiv g → is-equiv (map-prod f g)
    pr1
      ( pr1
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-prod sf sg
    pr2
      ( pr1
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( inv-htpy (map-prod-comp sf sg f g)) ∙h
      ( (htpy-map-prod Sf Sg) ∙h map-prod-id)
    pr1
      ( pr2
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) = map-prod rf rg
    pr2
      ( pr2
        ( is-equiv-map-prod f g
          ( pair (pair sf Sf) (pair rf Rf))
          ( pair (pair sg Sg) (pair rg Rg)))) =
      ( inv-htpy (map-prod-comp f g rf rg)) ∙h
      ( (htpy-map-prod Rf Rg) ∙h map-prod-id)

  equiv-prod : (f : A ≃ C) (g : B ≃ D) → (A × B) ≃ (C × D)
  pr1 (equiv-prod (pair f is-equiv-f) (pair g is-equiv-g)) = map-prod f g
  pr2 (equiv-prod (pair f is-equiv-f) (pair g is-equiv-g)) =
    is-equiv-map-prod f g is-equiv-f is-equiv-g
```

### TODO: title

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {X : UU l1} {A : UU l2} {B : UU l3} {C : UU l4} {D : UU l5}
  (f : X → A) (g : X → B) (u : X → C) (v : X → D) (s : A → C) (t : B → D)
  where

  -- TODO: prove facts about (map-prod f g ∘ diagonal) ≡ ⟨ f , g ⟩ somewhere else?
  htpy-comp-parallel-prod : (u ~ (s ∘ f)) → (v ~ (t ∘ g)) →
    ((map-prod u v ∘ diagonal X) ~ (map-prod s t ∘ (map-prod f g ∘ diagonal X)))
  htpy-comp-parallel-prod H K x = eq-pair (H x) (K x)

```

### The fibers of `map-prod f g`

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D)
  where
  
  map-compute-fib-map-prod :
    (t : C × D) → fib (map-prod f g) t → (fib f (pr1 t)) × (fib g (pr2 t))
  pr1
    ( pr1
      ( map-compute-fib-map-prod .(map-prod f g (pair a b))
        ( pair (pair a b) refl))) = a
  pr2
    ( pr1
      ( map-compute-fib-map-prod .(map-prod f g (pair a b))
        ( pair (pair a b) refl))) = refl
  pr1
    ( pr2
      ( map-compute-fib-map-prod .(map-prod f g (pair a b))
        ( pair (pair a b) refl))) = b
  pr2
    ( pr2
      ( map-compute-fib-map-prod .(map-prod f g (pair a b))
        ( pair (pair a b) refl))) = refl

  map-inv-compute-fib-map-prod :
    (t : C × D) → (fib f (pr1 t)) × (fib g (pr2 t)) → fib (map-prod f g) t
  pr1
    ( pr1
      ( map-inv-compute-fib-map-prod (pair .(f x) .(g y))
        ( pair (pair x refl) (pair y refl)))) = x
  pr2
    ( pr1
      ( map-inv-compute-fib-map-prod (pair .(f x) .(g y))
        ( pair (pair x refl) (pair y refl)))) = y
  pr2
    ( map-inv-compute-fib-map-prod (pair .(f x) .(g y))
      ( pair (pair x refl) (pair y refl))) = refl
  
  abstract
    issec-map-inv-compute-fib-map-prod :
      (t : C × D) →
      ((map-compute-fib-map-prod t) ∘ (map-inv-compute-fib-map-prod t)) ~ id
    issec-map-inv-compute-fib-map-prod (pair .(f x) .(g y))
      (pair (pair x refl) (pair y refl)) = refl

  abstract
    isretr-map-inv-compute-fib-map-prod :
      (t : C × D) →
      ((map-inv-compute-fib-map-prod t) ∘ (map-compute-fib-map-prod t)) ~ id
    isretr-map-inv-compute-fib-map-prod .(map-prod f g (pair a b))
      (pair (pair a b) refl) = refl

  abstract
    is-equiv-map-compute-fib-map-prod :
      (t : C × D) → is-equiv (map-compute-fib-map-prod t)
    is-equiv-map-compute-fib-map-prod t =
      is-equiv-has-inverse
        ( map-inv-compute-fib-map-prod t)
        ( issec-map-inv-compute-fib-map-prod t)
        ( isretr-map-inv-compute-fib-map-prod t)

  compute-fib-map-prod :
    (t : C × D) → fib (map-prod f g) t ≃ ((fib f (pr1 t)) × (fib g (pr2 t)))
  pr1 (compute-fib-map-prod t) = map-compute-fib-map-prod t
  pr2 (compute-fib-map-prod t) = is-equiv-map-compute-fib-map-prod t
```

### Product map is an equivalence if and only if factors are equivalences, assuming inhabited codomains

The idea behind the requirement of "inhabited codomains" is that it suffices
for one codomain to be empty to make the product empty, and in such situation
we cannot guarantee that the other map is an equivalence: consider the simple
counterexample of `id×ex-falso : 0×0 → 0×1`. Then the only way to show that
`ex-falso` is an equivalence is by assuming a contradiction `c : 0`.


```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D)
  where

  module _
    (e : is-equiv (map-prod f g))
    where

    private
      inv-f×g : has-inverse (map-prod f g)
      inv-f×g = has-inverse-is-equiv e
      inv-f×g-map : C × D → A × B
      inv-f×g-map = pr1 inv-f×g
      issec-inv-f×g-map : ((map-prod f g) ∘ inv-f×g-map) ~ id
      issec-inv-f×g-map = pr1 (pr2 inv-f×g)
      isretr-inv-f×g-map : (inv-f×g-map ∘ (map-prod f g)) ~ id
      isretr-inv-f×g-map = pr2 (pr2 inv-f×g)

    map-inv-left-factor-is-equiv-map-prod : D → C → A
    map-inv-left-factor-is-equiv-map-prod d c = pr1 (inv-f×g-map (pair c d))

    map-inv-right-factor-is-equiv-map-prod : C → D → B
    map-inv-right-factor-is-equiv-map-prod c d = pr2 (inv-f×g-map (pair c d))

    issec-map-inv-left-factor-is-equiv-map-prod : (d : D) →
      (f ∘ map-inv-left-factor-is-equiv-map-prod d) ~ id
    issec-map-inv-left-factor-is-equiv-map-prod d c = (pr1 ·l issec-inv-f×g-map) (pair c d)

    issec-map-inv-right-factor-is-equiv-map-prod : (c : C) →
      (g ∘ map-inv-right-factor-is-equiv-map-prod c) ~ id
    issec-map-inv-right-factor-is-equiv-map-prod c d = (pr2 ·l issec-inv-f×g-map) (pair c d)

    isretr-map-inv-left-factor-is-equiv-map-prod : (d : D) →
      (map-inv-left-factor-is-equiv-map-prod d ∘ f) ~ id
    isretr-map-inv-left-factor-is-equiv-map-prod d =
      ((pr1 ∘ inv-f×g-map) ·l htpy-triangle) ∙h
        ((pr1 ·l isretr-inv-f×g-map) ·r <id,const>)
      where
      across : A → B
      across a = map-inv-right-factor-is-equiv-map-prod (f a) d
      <id,const> : A → A × B
      <id,const> a = pair a (across a)
      htpy-triangle : (λ a → pair (f a) d) ~ ((map-prod f g) ∘ <id,const>)
      htpy-triangle a =
        eq-pair
          refl
          (inv-htpy (issec-map-inv-right-factor-is-equiv-map-prod (f a)) d)

    is-equiv-left-factor-is-equiv-map-prod : D → is-equiv f
    is-equiv-left-factor-is-equiv-map-prod d =
      is-equiv-has-inverse
        (map-inv-left-factor-is-equiv-map-prod d)
        (issec-map-inv-left-factor-is-equiv-map-prod d)
        (isretr-map-inv-left-factor-is-equiv-map-prod d)

    isretr-map-inv-right-factor-is-equiv-map-prod : (c : C) →
      (map-inv-right-factor-is-equiv-map-prod c ∘ g) ~ id
    isretr-map-inv-right-factor-is-equiv-map-prod c =
      ((pr2 ∘ inv-f×g-map) ·l htpy-triangle) ∙h
        ((pr2 ·l isretr-inv-f×g-map) ·r <const,id>)
      where
      across : B → A
      across b = map-inv-left-factor-is-equiv-map-prod (g b) c
      <const,id> : B → A × B
      <const,id> b = pair (across b) b
      htpy-triangle : (λ b → pair c (g b)) ~ ((map-prod f g) ∘ <const,id>)
      htpy-triangle b =
        eq-pair
          (inv-htpy (issec-map-inv-left-factor-is-equiv-map-prod (g b)) c)
          refl

    is-equiv-right-factor-is-equiv-map-prod : C → is-equiv g
    is-equiv-right-factor-is-equiv-map-prod c =
      is-equiv-has-inverse
        (map-inv-right-factor-is-equiv-map-prod c)
        (issec-map-inv-right-factor-is-equiv-map-prod c)
        (isretr-map-inv-right-factor-is-equiv-map-prod c)

  is-equiv-factors-is-equiv-map-prod :
    is-equiv (map-prod f g) → (D → is-equiv f) × (C → is-equiv g)
  pr1 (is-equiv-factors-is-equiv-map-prod e) =
    is-equiv-left-factor-is-equiv-map-prod e
  pr2 (is-equiv-factors-is-equiv-map-prod e) =
    is-equiv-right-factor-is-equiv-map-prod e

  module _
    (is-equiv-left-factor : D → is-equiv f)
    (is-equiv-right-factor : C → is-equiv g)
    where

    private
      inv-f : D → has-inverse f
      inv-f d = has-inverse-is-equiv (is-equiv-left-factor d)
      inv-f-map : D → C → A
      inv-f-map d = pr1 (inv-f d)
      issec-inv-f-map : (d : D) → (f ∘ (inv-f-map d)) ~ id
      issec-inv-f-map d = pr1 (pr2 (inv-f d))
      isretr-inv-f-map : (d : D) → ((inv-f-map d) ∘ f) ~ id
      isretr-inv-f-map d = pr2 (pr2 (inv-f d))
      inv-g : C → has-inverse g
      inv-g c = has-inverse-is-equiv (is-equiv-right-factor c)
      inv-g-map : C → D → B
      inv-g-map c = pr1 (inv-g c)
      issec-inv-g-map : (c : C) → (g ∘ (inv-g-map c)) ~ id
      issec-inv-g-map c = pr1 (pr2 (inv-g c))
      isretr-inv-g-map : (c : C) → ((inv-g-map c) ∘ g) ~ id
      isretr-inv-g-map c = pr2 (pr2 (inv-g c))

    map-inv-map-prod-is-equiv-factors : C × D → A × B
    pr1 (map-inv-map-prod-is-equiv-factors (pair c d)) =
      inv-f-map d c
    pr2 (map-inv-map-prod-is-equiv-factors (pair c d)) =
      inv-g-map c d

    issec-map-inv-map-prod-is-equiv-factors :
      (map-prod f g ∘ map-inv-map-prod-is-equiv-factors) ~ id
    issec-map-inv-map-prod-is-equiv-factors (pair c d) =
      eq-pair (issec-inv-f-map d c) (issec-inv-g-map c d)

    isretr-map-inv-map-prod-is-equiv-factors :
      (map-inv-map-prod-is-equiv-factors ∘ map-prod f g) ~ id
    isretr-map-inv-map-prod-is-equiv-factors (pair a b) =
      eq-pair (isretr-inv-f-map (g b) a) (isretr-inv-g-map (f a) b)

  is-equiv-map-prod-is-equiv-factors :
    (D → is-equiv f) → (C → is-equiv g) → is-equiv (map-prod f g)
  is-equiv-map-prod-is-equiv-factors f' g' =
    is-equiv-has-inverse
      (map-inv-map-prod-is-equiv-factors f' g')
      (issec-map-inv-map-prod-is-equiv-factors f' g')
      (isretr-map-inv-map-prod-is-equiv-factors f' g')
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
