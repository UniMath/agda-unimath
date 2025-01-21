# Perfect images

```agda
module foundation.perfect-images where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.connected-maps
open import foundation.coproduct-types
open import foundation.decidable-dependent-function-types
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-propositions
open import foundation.functoriality-dependent-function-types
open import foundation.iterated-dependent-product-types
open import foundation.iterating-functions
open import foundation.law-of-excluded-middle
open import foundation.mere-equality
open import foundation.negated-equality
open import foundation.negation
open import foundation.pi-0-trivial-maps
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience

open import foundation-core.cartesian-product-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.transport-along-identifications

open import logic.double-negation-eliminating-maps
open import logic.double-negation-elimination
open import logic.double-negation-stable-embeddings
```

</details>

## Idea

Consider two maps `f : A → B` and `g : B → A`. For `(g ◦ f)ⁿ(a₀) ＝ a`, consider
also the following chain

```text
      f          g            f               g       g
  a₀ --> f (a₀) --> g(f(a₀)) --> f(g(f(a₀))) --> ... --> (g ◦ f)ⁿ(a₀) ＝ a
```

We say `a₀` is an {{#concept "origin"}} for `a`, and `a` is a
{{#concept "perfect image" Agda=is-perfect-image}} for `g` if any origin of `a`
is in the [image](foundation.images.md) of `g`.

## Definitions

### Perfect images

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-perfect-image : (a : A) → UU (l1 ⊔ l2)
  is-perfect-image a =
    (a₀ : A) (n : ℕ) → iterate n (g ∘ f) a₀ ＝ a → fiber g a₀
```

An alternative but equivalent definition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-perfect-image-at' : A → ℕ → UU (l1 ⊔ l2)
  is-perfect-image-at' a n = (p : fiber (iterate n (g ∘ f)) a) → fiber g (pr1 p)

  is-perfect-image' : (a : A) → UU (l1 ⊔ l2)
  is-perfect-image' a =
    (n : ℕ) → is-perfect-image-at' a n

  compute-is-perfect-image :
    (a : A) → is-perfect-image' a ≃ is-perfect-image f g a
  compute-is-perfect-image a =
    equivalence-reasoning
    ((n : ℕ) (p : fiber (iterate n (g ∘ f)) a) → fiber g (pr1 p))
    ≃ ((n : ℕ) (a₀ : A) → iterate n (g ∘ f) a₀ ＝ a → fiber g a₀)
    by equiv-Π-equiv-family (λ n → equiv-ev-pair)
    ≃ ((a₀ : A) (n : ℕ) → iterate n (g ∘ f) a₀ ＝ a → fiber g a₀)
    by equiv-swap-Π
```

### Nonperfect images

We can talk about origins of `a` which are not images of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-nonperfect-image : (a : A) → UU (l1 ⊔ l2)
  is-nonperfect-image a =
    Σ A (λ a₀ → Σ ℕ (λ n → (iterate n (g ∘ f) a₀ ＝ a) × ¬ (fiber g a₀)))
```

### Nonperfect fibers over an element

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (g : B → A)
  where

  has-nonperfect-fiber : (b : B) → UU (l1 ⊔ l2)
  has-nonperfect-fiber b =
    Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))

  is-prop-has-nonperfect-fiber' :
    is-prop-map f → (b : B) → is-prop (has-nonperfect-fiber b)
  is-prop-has-nonperfect-fiber' F b = is-prop-Σ (F b) (λ _ → is-prop-neg)

  is-prop-has-nonperfect-fiber :
    is-emb f → (b : B) → is-prop (has-nonperfect-fiber b)
  is-prop-has-nonperfect-fiber F =
    is-prop-has-nonperfect-fiber' (is-prop-map-is-emb F)

  has-nonperfect-fiber-Prop' :
    is-prop-map f → (b : B) → Prop (l1 ⊔ l2)
  has-nonperfect-fiber-Prop' F b =
    ( has-nonperfect-fiber b , is-prop-has-nonperfect-fiber' F b)

  has-nonperfect-fiber-Prop :
    is-emb f → (b : B) → Prop (l1 ⊔ l2)
  has-nonperfect-fiber-Prop F b =
    ( has-nonperfect-fiber b , is-prop-has-nonperfect-fiber F b)
```

## Properties

TODO: prose here

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (is-emb-g : is-emb g)
  where

  is-prop-is-perfect-image-is-emb :
    (a : A) → is-prop (is-perfect-image f g a)
  is-prop-is-perfect-image-is-emb a =
    is-prop-iterated-Π 3 (λ a₀ n p → is-prop-map-is-emb is-emb-g a₀)

  is-perfect-image-Prop : A → Prop (l1 ⊔ l2)
  pr1 (is-perfect-image-Prop a) = is-perfect-image f g a
  pr2 (is-perfect-image-Prop a) = is-prop-is-perfect-image-is-emb a
```

If `a` is a perfect image for `g`, then `a` has a preimage under `g`. Just take
`n = zero` in the definition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  fiber-is-perfect-image : (a : A) → is-perfect-image f g a → fiber g a
  fiber-is-perfect-image a ρ = ρ a 0 refl
```

One can define a map from `A` to `B` restricting the domain to the perfect
images of `g`. This gives a kind of [section](foundation-core.sections.md) of
`g`. When `g` is also an embedding, the map gives a kind of
[retraction](foundation-core.retractions.md) of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  inverse-of-perfect-image : (a : A) → is-perfect-image f g a → B
  inverse-of-perfect-image a ρ = pr1 (fiber-is-perfect-image a ρ)

  is-section-inverse-of-perfect-image :
    (a : A) (ρ : is-perfect-image f g a) → g (inverse-of-perfect-image a ρ) ＝ a
  is-section-inverse-of-perfect-image a ρ = pr2 (fiber-is-perfect-image a ρ)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (G : is-injective g)
  where

  is-retraction-inverse-of-perfect-image :
    (b : B) (ρ : is-perfect-image f g (g b)) →
    inverse-of-perfect-image (g b) ρ ＝ b
  is-retraction-inverse-of-perfect-image b ρ =
    G (is-section-inverse-of-perfect-image (g b) ρ)
```

If `g(f(a))` is a perfect image for `g`, so is `a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  previous-perfect-image-at' :
    (a : A) (n : ℕ) →
    is-perfect-image-at' f g (g (f a)) (succ-ℕ n) →
    is-perfect-image-at' f g a n
  previous-perfect-image-at' a n γ (a₀ , p) = γ (a₀ , ap (g ∘ f) p)

  previous-perfect-image' :
    (a : A) → is-perfect-image' f g (g (f a)) → is-perfect-image' f g a
  previous-perfect-image' a γ n = previous-perfect-image-at' a n (γ (succ-ℕ n))

  previous-perfect-image :
    (a : A) → is-perfect-image f g (g (f a)) → is-perfect-image f g a
  previous-perfect-image a γ a₀ n p = γ a₀ (succ-ℕ n) (ap (g ∘ f) p)
```

Perfect images goes to a disjoint place under `inverse-of-perfect-image` than
`f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  perfect-image-has-distinct-image :
    (a a₀ : A) →
    ¬ (is-perfect-image f g a) →
    (ρ : is-perfect-image f g a₀) →
    f a ≠ inverse-of-perfect-image a₀ ρ
  perfect-image-has-distinct-image a a₀ nρ ρ p =
    v ρ
    where
    q : g (f a) ＝ a₀
    q = ap g p ∙ is-section-inverse-of-perfect-image a₀ ρ

    s : ¬ (is-perfect-image f g (g (f a)))
    s = λ η → nρ (previous-perfect-image a η)

    v : ¬ (is-perfect-image f g a₀)
    v = tr (λ a' → ¬ (is-perfect-image f g a')) q s
```

### The constructive story

If we assume that `g` is a double negation eliminating map, we can prove that if
`is-nonperfect-image a` does not hold, we have `is-perfect-image a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (G : is-double-negation-eliminating-map g)
  where

  double-negation-elim-is-perfect-image :
    (a : A) → ¬ (is-nonperfect-image a) → is-perfect-image f g a
  double-negation-elim-is-perfect-image a nρ a₀ n p =
    G a₀ (λ a₁ → nρ (a₀ , n , p , a₁))
```

The following property states that if `g (b)` is not a perfect image, then `b`
has an `f` fiber `a` that is not a perfect image for `g`. Again, we need to
assume law of excluded middle and that both `g` and `f` are embedding.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A}
  (G : is-double-negation-eliminating-map g)
  (b : B)
  (nρ : ¬ (is-perfect-image f g (g b)))
  where

  not-not-is-nonperfect-image : ¬¬ (is-nonperfect-image {f = f} (g b))
  not-not-is-nonperfect-image nμ =
    nρ (double-negation-elim-is-perfect-image G (g b) nμ)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (is-injective-g : is-injective g) (b : B)
  where

  has-nonperfect-fiber-is-nonperfect-image :
    is-nonperfect-image {f = f} (g b) → has-nonperfect-fiber f g b
  has-nonperfect-fiber-is-nonperfect-image (x₀ , zero-ℕ , u) =
    ex-falso (pr2 u (b , inv (pr1 u)))
  has-nonperfect-fiber-is-nonperfect-image (x₀ , succ-ℕ n , u) =
    ( iterate n (g ∘ f) x₀ , is-injective-g (pr1 u)) ,
    ( λ s → pr2 u (s x₀ n refl))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A}
  (is-double-negation-eliminating-g : is-double-negation-eliminating-map g)
  (is-injective-g : is-injective g)
  (b : B) (nρ : ¬ (is-perfect-image f g (g b)))
  where

  not-not-has-nonperfect-fiber-is-not-perfect-image :
    ¬¬ (has-nonperfect-fiber f g b)
  not-not-has-nonperfect-fiber-is-not-perfect-image t =
    not-not-is-nonperfect-image
      ( is-double-negation-eliminating-g)
      ( b)
      ( nρ)
      ( λ s → t (has-nonperfect-fiber-is-nonperfect-image is-injective-g b s))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A}
  (is-double-negation-eliminating-f : is-double-negation-eliminating-map f)
  (is-π₀-trivial-f : is-π₀-trivial-map' f)
  (b : B)
  where

  double-negation-elim-has-nonperfect-fiber :
    has-double-negation-elim (has-nonperfect-fiber f g b)
  double-negation-elim-has-nonperfect-fiber =
    double-negation-elim-Σ-all-elements-merely-equal-base
      ( is-π₀-trivial-f b)
      ( is-double-negation-eliminating-f b)
      ( λ p → double-negation-elim-neg (is-perfect-image f g (pr1 p)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A}
  (is-double-negation-eliminating-g : is-double-negation-eliminating-map g)
  (is-injective-g : is-injective g)
  (is-double-negation-eliminating-f : is-double-negation-eliminating-map f)
  (is-π₀-trivial-f : is-π₀-trivial-map' f)
  (b : B)
  (nρ : ¬ (is-perfect-image f g (g b)))
  where

  has-nonperfect-fiber-is-not-perfect-image :
    has-nonperfect-fiber f g b
  has-nonperfect-fiber-is-not-perfect-image =
    double-negation-elim-has-nonperfect-fiber
      ( is-double-negation-eliminating-f)
      ( is-π₀-trivial-f)
      ( b)
      ( not-not-has-nonperfect-fiber-is-not-perfect-image
        ( is-double-negation-eliminating-g)
        ( is-injective-g)
        ( b)
        ( nρ))

  fiber-has-nonperfect-fiber-is-not-perfect-image : fiber f b
  fiber-has-nonperfect-fiber-is-not-perfect-image =
    pr1 has-nonperfect-fiber-is-not-perfect-image

  element-has-nonperfect-fiber-is-not-perfect-image : A
  element-has-nonperfect-fiber-is-not-perfect-image =
    pr1 fiber-has-nonperfect-fiber-is-not-perfect-image

  is-in-fiber-element-has-nonperfect-fiber-is-not-perfect-image :
    f element-has-nonperfect-fiber-is-not-perfect-image ＝ b
  is-in-fiber-element-has-nonperfect-fiber-is-not-perfect-image =
    pr2 fiber-has-nonperfect-fiber-is-not-perfect-image

  is-not-perfect-image-has-nonperfect-fiber-is-not-perfect-image :
     ¬ (is-perfect-image f g element-has-nonperfect-fiber-is-not-perfect-image)
  is-not-perfect-image-has-nonperfect-fiber-is-not-perfect-image =
    pr2 has-nonperfect-fiber-is-not-perfect-image

module _
  {l1 : Level} {A : UU l1} {f : A → A}
  (is-decidable-f : is-decidable-map f)
  (is-π₀-trivial-f : is-π₀-trivial-map' f)
  where

  is-decidable-map-iterate-is-π₀-trivial-map' :
    (n : ℕ) → is-decidable-map (iterate n f)
  is-decidable-map-iterate-is-π₀-trivial-map' zero-ℕ = is-decidable-map-id
  is-decidable-map-iterate-is-π₀-trivial-map' (succ-ℕ n) =
    is-decidable-map-comp-is-π₀-trivial-map'
      ( is-π₀-trivial-f)
      ( is-decidable-f)
      ( is-decidable-map-iterate-is-π₀-trivial-map' n)

module _
  {l1 : Level} {A : UU l1} {f : A → A}
  (is-π₀-trivial-f : is-π₀-trivial-map' f)
  where

  is-π₀-trivial-map'-iterate :
    (n : ℕ) → is-π₀-trivial-map' (iterate n f)
  is-π₀-trivial-map'-iterate zero-ℕ = is-π₀-trivial-map'-id
  is-π₀-trivial-map'-iterate (succ-ℕ n) =
    is-π₀-trivial-map'-comp is-π₀-trivial-f (is-π₀-trivial-map'-iterate n)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G : is-decidable-emb g) (F : is-decidable-map f) (F' : is-π₀-trivial-map' f)
  where

  is-decidable-prop-is-perfect-image-at' :
    (a : A) (n : ℕ) → is-decidable-prop (is-perfect-image-at' f g a n)
  is-decidable-prop-is-perfect-image-at' a n =
    is-decidable-prop-Π-all-elements-merely-equal-base
      ( λ x →
        fiber g (pr1 x) ,
        is-decidable-prop-map-is-decidable-emb G (pr1 x))
      ( is-π₀-trivial-map'-iterate
        ( is-π₀-trivial-map'-comp
          ( is-π₀-trivial-map'-is-emb (is-emb-is-decidable-emb G))
          ( F'))
        ( n)
        ( a))
      ( is-decidable-map-iterate-is-π₀-trivial-map'
        ( is-decidable-map-comp-is-π₀-trivial-map'
          ( is-π₀-trivial-map'-is-emb (is-emb-is-decidable-emb G))
          ( is-decidable-map-is-decidable-emb G)
        ( F))
        ( is-π₀-trivial-map'-comp
          ( is-π₀-trivial-map'-is-emb (is-emb-is-decidable-emb G))
          ( F'))
        ( n)
        ( a))
```

### Assuming the weak limited principle of omniscience

```agda
module _
  {l1 l2 : Level}
  (wlpo : level-WLPO (l1 ⊔ l2))
  {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A}
  (G : is-decidable-emb g)
  (F : is-decidable-map f)
  (F' : is-π₀-trivial-map' f)
  where

  abstract
    is-decidable-is-perfect-image'-WLPO :
      (a : A) → is-decidable (is-perfect-image' f g a)
    is-decidable-is-perfect-image'-WLPO a =
      wlpo
        ( λ n →
          is-perfect-image-at' f g a n ,
          is-decidable-prop-is-perfect-image-at' G F F' a n)

  is-decidable-is-perfect-image-WLPO :
    (a : A) → is-decidable (is-perfect-image f g a)
  is-decidable-is-perfect-image-WLPO a =
    is-decidable-equiv'
      ( compute-is-perfect-image f g a)
      ( is-decidable-is-perfect-image'-WLPO a)
```

### The classical story

If `g` is an [embedding](foundation-core.embeddings.md), then
`is-perfect-image a` is a [proposition](foundation-core.propositions.md). In
this case, if we assume the
[law of exluded middle](foundation.law-of-excluded-middle.md), we can show
`is-perfect-image a` is a [decidable type](foundation.decidable-types.md) for
any `a : A`.

```agda
module _
  {l1 l2 : Level} (lem : LEM (l1 ⊔ l2)) {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (is-emb-g : is-emb g)
  where

  is-decidable-is-perfect-image-is-emb-LEM :
    (a : A) → is-decidable (is-perfect-image f g a)
  is-decidable-is-perfect-image-is-emb-LEM a =
    lem (is-perfect-image-Prop is-emb-g a)
```

If we assume the law of excluded middle and `g` is an embedding, we can prove
that if `is-nonperfect-image a` does not hold, we have `is-perfect-image a`.

```agda
module _
  {l1 l2 : Level} (lem : LEM (l1 ⊔ l2))
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (is-emb-g : is-emb g)
  where

  double-negation-elim-is-perfect-image-LEM :
    (a : A) → ¬ (is-nonperfect-image a) → is-perfect-image f g a
  double-negation-elim-is-perfect-image-LEM =
    double-negation-elim-is-perfect-image
      ( is-double-negation-eliminating-map-is-decidable-map
        ( λ y → lem (fiber g y , is-prop-map-is-emb is-emb-g y)))
```

The following property states that if `g (b)` is not a perfect image, then `b`
has an `f` fiber `a` that is not a perfect image for `g`. Again, we need to
assume law of excluded middle and that both `g` and `f` are embedding.

```agda
module _
  {l1 l2 : Level} (lem : LEM (l1 ⊔ l2))
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (is-emb-f : is-emb f) (is-emb-g : is-emb g)
  where

  has-nonperfect-fiber-is-not-perfect-image-LEM :
      (b : B) →
      ¬ (is-perfect-image f g (g b)) →
      has-nonperfect-fiber f g b
  has-nonperfect-fiber-is-not-perfect-image-LEM =
    has-nonperfect-fiber-is-not-perfect-image
      ( is-double-negation-eliminating-map-is-decidable-map
        ( λ y → lem (fiber g y , is-prop-map-is-emb is-emb-g y)))
      ( is-injective-is-emb is-emb-g)
      ( is-double-negation-eliminating-map-is-decidable-map
        ( λ y → lem (fiber f y , is-prop-map-is-emb is-emb-f y)))
      ( λ y p q → mere-eq-eq (eq-is-prop (is-prop-map-is-emb is-emb-f y)))
```
