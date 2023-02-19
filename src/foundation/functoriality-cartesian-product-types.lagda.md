#  Functoriality of cartesian product types

```agda
module foundation.functoriality-cartesian-product-types where

open import foundation-core.constant-maps
open import foundation-core.cartesian-product-types
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

### TODO: title

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (f : A → C) (g : B → D)
  where

  module _
    ((pair (pair s-fg S-fg) (pair r-fg R-fg)) : is-equiv (map-prod f g))
    where

    -- TODO: "component" sounds weird
    sec-map-prod-component-pr1 : D → sec f
    pr1 (sec-map-prod-component-pr1 d) c = pr1 (s-fg (pair c d))
    pr2 (sec-map-prod-component-pr1 d) c = (pr1 ·l S-fg) (pair c d)

    sec-map-prod-component-pr2 : C → sec g
    pr1 (sec-map-prod-component-pr2 c) d = pr2 (s-fg (pair c d))
    pr2 (sec-map-prod-component-pr2 c) d = (pr2 ·l S-fg) (pair c d)

    retr-map-prod-component-pr1 : D → retr f
    pr1 (retr-map-prod-component-pr1 d) c = pr1 (r-fg (pair c d))
    pr2 (retr-map-prod-component-pr1 d) =
      ((pr1 ∘ r-fg) ·l triangle-sec) ∙h ((pr1 ·l R-fg) ·r id×const)
      where
      get-sec-g : A → sec g
      get-sec-g a = sec-map-prod-component-pr2 (f a)
      across : A → B
      across a = pr1 (get-sec-g a) d
      id×const : A → A × B
      id×const = map-prod id across ∘ diagonal _
      triangle-sec : (map-prod f (const _ _ _ d) ∘ diagonal _) ~ ((map-prod f g) ∘ id×const)
      triangle-sec =
        htpy-comp-parallel-prod
          id across
          _ _
          f g
          refl-htpy (inv-htpy (λ a → (pr2 (get-sec-g a)) d))

    -- TODO: which looks better
    retr-map-prod-component-pr2 : C → retr g
    pr1 (retr-map-prod-component-pr2 c) d = pr2 (r-fg (pair c d))
    pr2 (retr-map-prod-component-pr2 c) =
       ((pr2 ∘ r-fg) ·l triangle-sec) ∙h ((pr2 ·l R-fg) ·r const×id)
      where
      get-sec-f : B → sec f
      get-sec-f b = sec-map-prod-component-pr1 (g b)
      const×id : B → A × B
      const×id b = (pair (pr1 (get-sec-f b) c) b)
      triangle-sec : (λ b → (pair c (g b))) ~ ((map-prod f g) ∘ const×id)
      triangle-sec b = eq-pair (inv-htpy (pr2 (get-sec-f b)) c) refl

  prod-equivs-nonempty-codoms-is-equiv-map-prod :
    is-equiv (map-prod f g) → (D → is-equiv f) × (C → is-equiv g)
  pr1 (pr1 (prod-equivs-nonempty-codoms-is-equiv-map-prod e) d) =
    sec-map-prod-component-pr1 e d
  pr2 (pr1 (prod-equivs-nonempty-codoms-is-equiv-map-prod e) d) =
    retr-map-prod-component-pr1 e d
  pr1 (pr2 (prod-equivs-nonempty-codoms-is-equiv-map-prod e) c) =
    sec-map-prod-component-pr2 e c
  pr2 (pr2 (prod-equivs-nonempty-codoms-is-equiv-map-prod e) c) =
    retr-map-prod-component-pr2 e c

  is-equiv-map-prod-equivs-nonempty-codom' :
    (C × D) → (D → is-equiv f) → (C → is-equiv g) → is-equiv (map-prod f g)
  is-equiv-map-prod-equivs-nonempty-codom' (pair c d) f' g' =
    is-equiv-map-prod f g (f' d) (g' c)

  is-equiv-map-prod-equivs-nonempty-codoms :
    ((D → is-equiv f) × (C → is-equiv g)) → is-equiv (map-prod f g)
  pr1 (pr1 (is-equiv-map-prod-equivs-nonempty-codoms (pair f' g'))) cd =
    pr1 (pr1 (is-equiv-map-prod-equivs-nonempty-codom' cd f' g')) cd
  pr2 (pr1 (is-equiv-map-prod-equivs-nonempty-codoms (pair f' g'))) cd =
    pr2 (pr1 ((is-equiv-map-prod-equivs-nonempty-codom' cd f' g'))) cd
  pr1 (pr2 (is-equiv-map-prod-equivs-nonempty-codoms (pair f' g'))) cd =
    pr1 (pr2 (is-equiv-map-prod-equivs-nonempty-codom' cd f' g')) cd
  pr2 (pr2 (is-equiv-map-prod-equivs-nonempty-codoms (pair f' g'))) ab =
    pr2 (pr2 (is-equiv-map-prod-equivs-nonempty-codom' (map-prod f g ab) f' g')) ab
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
