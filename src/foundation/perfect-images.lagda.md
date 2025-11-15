# Perfect images

```agda
module foundation.perfect-images where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.decidable-dependent-function-types
open import foundation.decidable-embeddings
open import foundation.decidable-maps
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-dense-equality-maps
open import foundation.functoriality-dependent-function-types
open import foundation.iterating-functions
open import foundation.negated-equality
open import foundation.negation
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
open import logic.propositionally-decidable-maps
```

</details>

## Idea

Given two maps `f : A → B` and `g : B → A`, then if `(g ◦ f)ⁿ(a₀) ＝ a` for some
[natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`, we have a
chain of elements

```text
      f          g            f               g       g
  a₀ --> f (a₀) --> g(f(a₀)) --> f(g(f(a₀))) --> ... --> (g ◦ f)ⁿ(a₀) ＝ a.
```

We say `a₀` is an {{#concept "origin" Disambiguation="perfect image"}} for `a`,
and `a` is a {{#concept "perfect image" Agda=is-perfect-image}} for `g`
_relative to `f`_ if any origin of `a` is in the [image](foundation.images.md)
of `g`.

This concept is used in the
[Cantor–Schröder–Bernstein construction](foundation.cantor-schroder-bernstein-decidable-embeddings.md)
to construct an equivalence of types `A ≃ B` given mutual embeddings
`f : A ↪ B` and `g : B ↪ A`.

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
  is-perfect-image' a = (n : ℕ) → is-perfect-image-at' a n

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

We say an origin of `a` is a
{{#concept "nonperfect image" Disambiguation="of pair of mutually converse maps" Agda=is-nonperfect-image}}
if we have an `a₀ : A` and a natural number `n : ℕ` such that
`(g ∘ f)ⁿ(a₀) = a`, but the fiber of `g` above `a₀` is
[empty](foundation.empty-types.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-nonperfect-image : (a : A) → UU (l1 ⊔ l2)
  is-nonperfect-image a =
    Σ ℕ (λ n → Σ A (λ a₀ → (iterate n (g ∘ f) a₀ ＝ a) × ¬ (fiber g a₀)))
```

**Comment.** Notice that, while being a nonperfect image is not always a
proposition when `f` and `g` are embeddings, if we in addition require that `n`
be minimal this would make it propositional.

### Nonperfect fibers

We say `f` has a
{{#concept "nonperfect fiber" Disambiguation="of pair of mutually converse maps" Agda=has-nonperfect-fiber}}
over an element `b` if there is a nonperfect image in its fiber.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  has-not-perfect-fiber : B → UU (l1 ⊔ l2)
  has-not-perfect-fiber b =
    Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))

  has-nonperfect-fiber : B → UU (l1 ⊔ l2)
  has-nonperfect-fiber b =
    Σ (fiber f b) (λ s → is-nonperfect-image f g (pr1 s))
```

## Properties

### If `g` is an embedding then being a perfect image of `g` is a property

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-prop-is-perfect-image-at'' :
    is-prop-map g → (a : A) (n : ℕ) →
    is-prop (is-perfect-image-at' f g a n)
  is-prop-is-perfect-image-at'' G a n =
    is-prop-Π (λ p → G (pr1 p))

  is-prop-is-perfect-image' :
    is-prop-map g → (a : A) → is-prop (is-perfect-image f g a)
  is-prop-is-perfect-image' G a =
    is-prop-Π (λ a₀ → is-prop-Π (λ n → is-prop-Π (λ p → G a₀)))

  is-perfect-image-Prop' : is-prop-map g → A → Prop (l1 ⊔ l2)
  is-perfect-image-Prop' G a =
    ( is-perfect-image f g a , is-prop-is-perfect-image' G a)

  is-prop-is-perfect-image :
    is-emb g → (a : A) → is-prop (is-perfect-image f g a)
  is-prop-is-perfect-image G =
    is-prop-is-perfect-image' (is-prop-map-is-emb G)

  is-perfect-image-Prop : is-emb g → A → Prop (l1 ⊔ l2)
  is-perfect-image-Prop G a =
    ( is-perfect-image f g a , is-prop-is-perfect-image G a)
```

### If `f` is an embedding then having a not perfect fiber is a proposition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-prop-has-not-perfect-fiber' :
    is-prop-map f → (b : B) → is-prop (has-not-perfect-fiber f g b)
  is-prop-has-not-perfect-fiber' F b = is-prop-Σ (F b) (λ _ → is-prop-neg)

  is-prop-has-not-perfect-fiber :
    is-emb f → (b : B) → is-prop (has-not-perfect-fiber f g b)
  is-prop-has-not-perfect-fiber F =
    is-prop-has-not-perfect-fiber' (is-prop-map-is-emb F)

  has-not-perfect-fiber-Prop' :
    is-prop-map f → B → Prop (l1 ⊔ l2)
  has-not-perfect-fiber-Prop' F b =
    ( has-not-perfect-fiber f g b , is-prop-has-not-perfect-fiber' F b)

  has-not-perfect-fiber-Prop :
    is-emb f → B → Prop (l1 ⊔ l2)
  has-not-perfect-fiber-Prop F b =
    ( has-not-perfect-fiber f g b , is-prop-has-not-perfect-fiber F b)
```

### Fibers over perfect images

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
    (a : A) (ρ : is-perfect-image f g a) →
    g (inverse-of-perfect-image a ρ) ＝ a
  is-section-inverse-of-perfect-image a ρ =
    pr2 (fiber-is-perfect-image a ρ)
```

When `g` is also injective, the map gives a kind of
[retraction](foundation-core.retractions.md) of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-retraction-inverse-of-perfect-image :
    is-injective g →
    (b : B) (ρ : is-perfect-image f g (g b)) →
    inverse-of-perfect-image (g b) ρ ＝ b
  is-retraction-inverse-of-perfect-image G b ρ =
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
  previous-perfect-image-at' a n γ (a₀ , p) =
    γ (a₀ , ap (g ∘ f) p)

  previous-perfect-image' :
    (a : A) →
    is-perfect-image' f g (g (f a)) →
    is-perfect-image' f g a
  previous-perfect-image' a γ n =
    previous-perfect-image-at' a n (γ (succ-ℕ n))

  previous-perfect-image :
    (a : A) →
    is-perfect-image f g (g (f a)) →
    is-perfect-image f g a
  previous-perfect-image a γ a₀ n p =
    γ a₀ (succ-ℕ n) (ap (g ∘ f) p)
```

Perfect images of `g` relative to `f` not mapped to the image of `f` under
`inverse-of-perfect-image`.

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

### Double negation elimination on not perfect fibers

If we assume that `g` is a double negation eliminating map, we can prove that if
`is-nonperfect-image a` does not hold, then we have `is-perfect-image a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  double-negation-elim-is-perfect-image :
    is-double-negation-eliminating-map g →
    (a : A) → ¬ (is-nonperfect-image f g a) → is-perfect-image f g a
  double-negation-elim-is-perfect-image G a nρ a₀ n p =
    G a₀ (λ a₁ → nρ (n , a₀ , p , a₁))
```

If `g(b)` is not a perfect image, then there is an `a ∈ fiber f b` that is not a
perfect image of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-irrefutable-is-nonperfect-image-is-not-perfect-image :
    (G : is-double-negation-eliminating-map g)
    (b : B) (nρ : ¬ (is-perfect-image f g (g b))) →
    ¬¬ (is-nonperfect-image f g (g b))
  is-irrefutable-is-nonperfect-image-is-not-perfect-image G b nρ nμ =
    nρ (double-negation-elim-is-perfect-image G (g b) nμ)

  has-not-perfect-fiber-is-nonperfect-image :
    is-injective g →
    (b : B) →
    is-nonperfect-image f g (g b) →
    has-not-perfect-fiber f g b
  has-not-perfect-fiber-is-nonperfect-image G b (zero-ℕ , x₀ , u) =
    ex-falso (pr2 u (b , inv (pr1 u)))
  has-not-perfect-fiber-is-nonperfect-image G b (succ-ℕ n , x₀ , u) =
    ( iterate n (g ∘ f) x₀ , G (pr1 u)) ,
    ( λ s → pr2 u (s x₀ n refl))

  is-irrefutable-has-not-perfect-fiber-is-not-perfect-image :
    is-double-negation-eliminating-map g →
    is-injective g →
    (b : B) (nρ : ¬ (is-perfect-image f g (g b))) →
    ¬¬ (has-not-perfect-fiber f g b)
  is-irrefutable-has-not-perfect-fiber-is-not-perfect-image G G' b nρ t =
    is-irrefutable-is-nonperfect-image-is-not-perfect-image G b nρ
      ( λ s → t (has-not-perfect-fiber-is-nonperfect-image G' b s))
```

If `f` has double negation dense equality and double negation elimination, then
`has-not-perfect-fiber f g b` has double negation elimination.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  double-negation-elim-has-not-perfect-fiber :
    is-double-negation-eliminating-map f →
    has-double-negation-dense-equality-map f →
    (b : B) →
    has-double-negation-elim (has-not-perfect-fiber f g b)
  double-negation-elim-has-not-perfect-fiber F F' b =
    double-negation-elim-Σ-has-double-negation-dense-equality-base
      ( F' b)
      ( F b)
      ( λ p → double-negation-elim-neg (is-perfect-image f g (pr1 p)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  (G : is-double-negation-eliminating-map g)
  (G' : is-injective g)
  (F : is-double-negation-eliminating-map f)
  (F' : has-double-negation-dense-equality-map f)
  (b : B) (nρ : ¬ (is-perfect-image f g (g b)))
  where

  has-not-perfect-fiber-is-not-perfect-image :
    has-not-perfect-fiber f g b
  has-not-perfect-fiber-is-not-perfect-image =
    double-negation-elim-has-not-perfect-fiber F F' b
      ( is-irrefutable-has-not-perfect-fiber-is-not-perfect-image G G' b nρ)

  fiber-has-not-perfect-fiber-is-not-perfect-image : fiber f b
  fiber-has-not-perfect-fiber-is-not-perfect-image =
    pr1 has-not-perfect-fiber-is-not-perfect-image

  element-has-not-perfect-fiber-is-not-perfect-image : A
  element-has-not-perfect-fiber-is-not-perfect-image =
    pr1 fiber-has-not-perfect-fiber-is-not-perfect-image

  is-in-fiber-element-has-not-perfect-fiber-is-not-perfect-image :
    f element-has-not-perfect-fiber-is-not-perfect-image ＝ b
  is-in-fiber-element-has-not-perfect-fiber-is-not-perfect-image =
    pr2 fiber-has-not-perfect-fiber-is-not-perfect-image

  is-not-perfect-image-has-not-perfect-fiber-is-not-perfect-image :
    ¬ (is-perfect-image f g element-has-not-perfect-fiber-is-not-perfect-image)
  is-not-perfect-image-has-not-perfect-fiber-is-not-perfect-image =
    pr2 has-not-perfect-fiber-is-not-perfect-image
```

### Decidability of perfect images

Assuming `g` and `f` are decidable embedding, then for every natural number
`n : ℕ` and every element `a : A` it is decidable whether `a` is a perfect image
of `g` relative to `f` after `n` iterations. In fact, the map `f` need only be
propositionally decidable and have double negation dense equality on fibers.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where abstract

  is-decidable-prop-is-perfect-image-at'' :
    is-decidable-emb g →
    is-inhabited-or-empty-map f →
    has-double-negation-dense-equality-map f →
    (a : A) (n : ℕ) →
    is-decidable-prop (is-perfect-image-at' f g a n)
  is-decidable-prop-is-perfect-image-at'' G F F' a n =
    is-decidable-prop-Π-has-double-negation-dense-equality-base'
      ( λ x →
        fiber g (pr1 x) ,
        is-decidable-prop-map-is-decidable-emb G (pr1 x))
      ( has-double-negation-dense-equality-map-iterate
        ( has-double-negation-dense-equality-map-comp
          ( has-double-negation-dense-equality-map-is-emb
            ( is-emb-is-decidable-emb G))
          ( F'))
        ( n)
        ( a))
      ( is-inhabited-or-empty-map-iterate-has-double-negation-dense-equality-map
        ( is-inhabited-or-empty-map-comp-has-double-negation-dense-equality-map
          ( has-double-negation-dense-equality-map-is-emb
            ( is-emb-is-decidable-emb G))
          ( is-inhabited-or-empty-map-is-decidable-map
            ( is-decidable-map-is-decidable-emb G))
          ( F))
        ( has-double-negation-dense-equality-map-comp
          ( has-double-negation-dense-equality-map-is-emb
            ( is-emb-is-decidable-emb G))
          ( F'))
        ( n)
        ( a))

  is-decidable-prop-is-perfect-image-at' :
    is-decidable-emb g →
    is-decidable-map f →
    has-double-negation-dense-equality-map f →
    (a : A) (n : ℕ) →
    is-decidable-prop (is-perfect-image-at' f g a n)
  is-decidable-prop-is-perfect-image-at' G F =
    is-decidable-prop-is-perfect-image-at'' G
      ( is-inhabited-or-empty-map-is-decidable-map F)
```

### Decidability of perfect images under WLPO

It follows from the
[weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
that, for every pair of mutual decidable embeddings `f : A ↪ B` and
`g : B ↪ A`, it is decidable for every element `x : A` whether `x` is a perfect
image of `g` relative to `f`.

```agda
module _
  {l1 l2 : Level} (wlpo : level-WLPO (l1 ⊔ l2))
  {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where abstract

  is-decidable-is-perfect-image'-WLPO :
    is-decidable-emb g →
    is-decidable-map f →
    has-double-negation-dense-equality-map f →
    (a : A) →
    is-decidable (is-perfect-image' f g a)
  is-decidable-is-perfect-image'-WLPO G F F' a =
    wlpo
      ( λ n →
        is-perfect-image-at' f g a n ,
        is-decidable-prop-is-perfect-image-at' G F F' a n)

  is-decidable-is-perfect-image-WLPO :
    is-decidable-emb g →
    is-decidable-map f →
    has-double-negation-dense-equality-map f →
    (a : A) →
    is-decidable (is-perfect-image f g a)
  is-decidable-is-perfect-image-WLPO G F F' a =
    is-decidable-equiv'
      ( compute-is-perfect-image f g a)
      ( is-decidable-is-perfect-image'-WLPO G F F' a)
```

## External links

- See also the twin formalization in TypeTopology at
  [`CantorSchroederBernstein.PerfectImages`](https://martinescardo.github.io/TypeTopology/CantorSchroederBernstein.PerfectImages.html).
