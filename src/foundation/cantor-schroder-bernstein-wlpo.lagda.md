# The Cantor–Schröder–Bernstein-WLPO theorem

```agda
module foundation.cantor-schroder-bernstein-wlpo where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.injective-maps
open import foundation.law-of-excluded-middle
open import foundation.perfect-images
open import foundation.pi-0-trivial-maps
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.negation
open import foundation-core.sets

open import logic.double-negation-eliminating-maps
open import logic.double-negation-stable-embeddings
```

</details>

## Idea

> TODO

## Construction

Given a pair of mutual maps `f : A → B` and `g : B → A` such that

1. `f` and `g` satisfy double negation elimination on their fibers
2. For every element `x : A` it is decidable wheter `x` is a perfect image of
   `g` relative to `f`
3. `g` is injective
4. `f` is π₀-trivial

Then `B` is a retract of `A`. If `f` moreover is injective, then this retract is
an equivalence.

```agda
module _
  {l1 l2 : Level}
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (F : is-double-negation-eliminating-map f)
  (G : is-double-negation-eliminating-map g)
  (G' : is-injective g)
  where

  map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein :
    (x : A) → is-decidable (is-perfect-image f g x) → B
  map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein x (inl y) =
    inverse-of-perfect-image x y
  map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein x (inr y) =
    f x

  compute-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein :
    (y : B) →
    (γ : is-perfect-image f g (g y)) →
    (d : is-decidable (is-perfect-image f g (g y))) →
    map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
      ( g y) d ＝
    y
  compute-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein y γ
    ( inl v') =
    is-retraction-inverse-of-perfect-image G' y v'
  compute-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein y γ
    ( inr v) =
    ex-falso (v γ)

  compute-map-construction-is-not-perfect-image-Cantor-Schröder-Bernstein :
    (F' : is-π₀-trivial-map' f) →
    (y : B) →
    (nγ : ¬ (is-perfect-image f g (g y))) →
    (d :
      is-decidable
        ( is-perfect-image f g
          ( element-has-nonperfect-fiber-is-not-perfect-image
              G G' F F' y nγ))) →
    map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
      ( element-has-nonperfect-fiber-is-not-perfect-image G G' F F' y nγ)
      ( d) ＝
    y
  compute-map-construction-is-not-perfect-image-Cantor-Schröder-Bernstein
    F' y nγ (inl v) =
    ex-falso
      ( is-not-perfect-image-has-nonperfect-fiber-is-not-perfect-image
          G G' F F' y nγ v)
  compute-map-construction-is-not-perfect-image-Cantor-Schröder-Bernstein
    F' y nγ (inr _) =
    is-in-fiber-element-has-nonperfect-fiber-is-not-perfect-image
      G G' F F' y nγ

  map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein :
    (F' : is-π₀-trivial-map' f) →
    (y : B) → is-decidable (is-perfect-image f g (g y)) → A
  map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
    F' y (inl _) = g y
  map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
    F' y (inr nγ) =
    element-has-nonperfect-fiber-is-not-perfect-image G G' F F' y nγ

  is-section-map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein :
    (F' : is-π₀-trivial-map' f) →
    (y : B)
    (d : is-decidable (is-perfect-image f g (g y))) →
    (d' :
      is-decidable
        ( is-perfect-image f g
          ( map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
              F' y d))) →
    map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
      ( map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
          F' y d)
      ( d') ＝
    y
  is-section-map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein F' y (inl γ) =
    compute-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein y γ
  is-section-map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein F' y (inr nγ) =
    compute-map-construction-is-not-perfect-image-Cantor-Schröder-Bernstein
        F' y nγ

  map-construction-Cantor-Schröder-Bernstein :
    (D : (x : A) → is-decidable (is-perfect-image f g x)) → A → B
  map-construction-Cantor-Schröder-Bernstein D x =
    map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein x (D x)

  map-section-construction-Cantor-Schröder-Bernstein :
    (F' : is-π₀-trivial-map' f) →
    (D : (y : B) → is-decidable (is-perfect-image f g (g y))) → B → A
  map-section-construction-Cantor-Schröder-Bernstein F' D y =
    map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
      ( F')
      ( y)
      ( D y)

  is-section-map-section-construction-Cantor-Schröder-Bernstein :
    (F' : is-π₀-trivial-map' f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    is-section
      ( map-construction-Cantor-Schröder-Bernstein D)
      ( map-section-construction-Cantor-Schröder-Bernstein F' (D ∘ g))
  is-section-map-section-construction-Cantor-Schröder-Bernstein F' D y =
    is-section-map-section-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
      ( F')
      ( y)
      ( D (g y))
      ( D (map-section-construction-Cantor-Schröder-Bernstein F' (D ∘ g) y))

  section-construction-Cantor-Schröder-Bernstein :
    (F' : is-π₀-trivial-map' f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    section (map-construction-Cantor-Schröder-Bernstein D)
  section-construction-Cantor-Schröder-Bernstein F' D =
    map-section-construction-Cantor-Schröder-Bernstein F' (D ∘ g) ,
    is-section-map-section-construction-Cantor-Schröder-Bernstein F' D
```

Injectivity of the constructed map.

```agda
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein :
    (F' : is-injective f) →
    {x x' : A}
    (d : is-decidable (is-perfect-image f g x))
    (d' : is-decidable (is-perfect-image f g x')) →
    ( map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein x d) ＝
    ( map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein x' d') →
    x ＝ x'
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
    F' { x} {x'} (inl ρ) (inl ρ') p =
    ( inv (is-section-inverse-of-perfect-image x ρ)) ∙
    ( ap g p ∙
      is-section-inverse-of-perfect-image x' ρ')
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
    F' {x} {x'} (inl ρ) (inr nρ') p =
    ex-falso (perfect-image-has-distinct-image x' x nρ' ρ (inv p))
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
    F' { x} {x'} (inr nρ) (inl ρ') p =
    ex-falso (perfect-image-has-distinct-image x x' nρ ρ' p)
  is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
    F' {lx} {x'} (inr nρ) (inr nρ') p = F' p -- TODO: find alternative approach avoiding `is-injective f`
```

Piecing it all together.

```agda
  is-equiv-map-construction-Cantor-Schröder-Bernstein :
    (F' : is-π₀-trivial-map' f) →
    (F'' : is-injective f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    is-equiv (map-construction-Cantor-Schröder-Bernstein D)
  is-equiv-map-construction-Cantor-Schröder-Bernstein
    F' F'' D =
    is-equiv-is-injective
      ( section-construction-Cantor-Schröder-Bernstein F' D)
      ( λ {x} {x'} →
        is-injective-map-construction-is-decidable-is-perfect-image-Cantor-Schröder-Bernstein
          ( F'')
          ( D x)
          ( D x'))

  equiv-construction-Cantor-Schröder-Bernstein :
    (F' : is-π₀-trivial-map' f) →
    (F'' : is-injective f) →
    (D : (x : A) → is-decidable (is-perfect-image f g x)) →
    A ≃ B
  equiv-construction-Cantor-Schröder-Bernstein F' F'' D =
    map-construction-Cantor-Schröder-Bernstein D ,
    is-equiv-map-construction-Cantor-Schröder-Bernstein F' F'' D
```

## Theorem

### The Cantor-Schröder-Bernstein-Escardó theorem assuming the weak limited principle of omniscience

Assuming the weak limited principle of omniscience, then for every pair of
mutual decidable embeddings `f : A ↪ B` and `g : B ↪ A` it is decidable for
every element `x : A` whether it is a perfect image of `g` relative to `f`.
Therefore, `A ≃ B`.

In fact, it suffices to assume that `f` is decidable, π₀-trivial, and injective.

```agda
generalized-Cantor-Schröder-Bernstein-WLPO :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G : is-decidable-emb g) →
  (F : is-decidable-map f) (F' : is-π₀-trivial-map' f) (F'' : is-injective f) →
  A ≃ B
generalized-Cantor-Schröder-Bernstein-WLPO wlpo G F F' F'' =
  equiv-construction-Cantor-Schröder-Bernstein
    ( is-double-negation-eliminating-map-is-decidable-map F)
    ( is-double-negation-eliminating-map-is-decidable-emb G)
    ( is-injective-is-decidable-emb G)
    ( F')
    ( F'')
    ( is-decidable-is-perfect-image-WLPO wlpo
      ( G)
      ( F)
      ( F'))

Cantor-Schröder-Bernstein-WLPO' :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G : is-decidable-emb g) (F : is-decidable-emb f) →
  A ≃ B
Cantor-Schröder-Bernstein-WLPO' wlpo G F =
  generalized-Cantor-Schröder-Bernstein-WLPO wlpo G
    ( is-decidable-map-is-decidable-emb F)
    ( is-π₀-trivial-map'-is-emb (is-emb-is-decidable-emb F))
    ( is-injective-is-decidable-emb F)

Cantor-Schröder-Bernstein-WLPO :
  {l1 l2 : Level} → level-WLPO (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} → (A ↪ᵈ B) → (B ↪ᵈ A) → A ≃ B
Cantor-Schröder-Bernstein-WLPO wlpo (f , F) (g , G) =
  Cantor-Schröder-Bernstein-WLPO' wlpo G F
```

### The generalized Cantor-Schröder-Bernstein-Escardó theorem assuming the law of excluded middle

Assuming the law of excluded middle, then given two types `A` and `B` such that
there is a π₀-trivial injection `A → B` and an embedding `B ↪ A`, then `A` and
`B` are equivalent.

```text
generalized-Cantor-Schröder-Bernstein-LEM :
  {l1 l2 : Level} → LEM (l1 ⊔ l2) →
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (F : is-π₀-trivial-map' f) →
  (F' : is-injective f) →
  (G : is-emb g) →
  A ≃ B
generalized-Cantor-Schröder-Bernstein-LEM lem F F' G = {! equiv-construction-Cantor-Schröder-Bernstein   !}
```
