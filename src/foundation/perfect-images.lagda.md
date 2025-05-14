# Perfect images

```agda
module foundation.perfect-images where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.iterated-dependent-product-types
open import foundation.iterating-functions
open import foundation.law-of-excluded-middle
open import foundation.negated-equality
open import foundation.negation
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.embeddings
open import foundation-core.empty-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositional-maps
open import foundation-core.propositions
open import foundation-core.transport-along-identifications
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

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-perfect-image : (a : A) → UU (l1 ⊔ l2)
  is-perfect-image a =
    (a₀ : A) (n : ℕ) → (iterate n (g ∘ f)) a₀ ＝ a → fiber g a₀
```

## Properties

If `g` is an [embedding](foundation-core.embeddings.md), then
`is-perfect-image a` is a [proposition](foundation-core.propositions.md). In
this case, if we assume the
[law of excluded middle](foundation.law-of-excluded-middle.md), we can show
`is-perfect-image a` is a [decidable type](foundation.decidable-types.md) for
any `a : A`.

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

  is-decidable-is-perfect-image-is-emb :
    LEM (l1 ⊔ l2) → (a : A) → is-decidable (is-perfect-image f g a)
  is-decidable-is-perfect-image-is-emb lem a =
    lem (is-perfect-image-Prop a)
```

If `a` is a perfect image for `g`, then `a` has a preimage under `g`. Just take
`n = zero` in the definition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-perfect-image-is-fiber :
    {f : A → B} {g : B → A} → (a : A) →
    is-perfect-image f g a → fiber g a
  is-perfect-image-is-fiber a ρ = ρ a 0 refl
```

One can define a map from `A` to `B` restricting the domain to the perfect
images of `g`. This gives a kind of [section](foundation-core.sections.md) of g.
When g is also an embedding, the map gives a kind of
[retraction](foundation-core.retractions.md) of g.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  inverse-of-perfect-image :
    (a : A) → (is-perfect-image f g a) → B
  inverse-of-perfect-image a ρ =
    pr1 (is-perfect-image-is-fiber a ρ)

  is-section-inverse-of-perfect-image :
    (a : A) (ρ : is-perfect-image f g a) →
    g (inverse-of-perfect-image a ρ) ＝ a
  is-section-inverse-of-perfect-image a ρ =
    pr2 (is-perfect-image-is-fiber a ρ)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} {is-emb-g : is-emb g}
  where

  is-retraction-inverse-of-perfect-image :
    (b : B) (ρ : is-perfect-image f g (g b)) →
    inverse-of-perfect-image (g b) ρ ＝ b
  is-retraction-inverse-of-perfect-image b ρ =
    is-injective-is-emb
      is-emb-g
      (is-section-inverse-of-perfect-image (g b) ρ)
```

If `g(f(a))` is a perfect image for `g`, so is `a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  previous-perfect-image :
    (a : A) →
    is-perfect-image f g (g (f (a))) →
    is-perfect-image f g a
  previous-perfect-image a γ a₀ n p = γ a₀ (succ-ℕ n) (ap (g ∘ f) p)
```

Perfect images goes to a disjoint place under `inverse-of-perfect-image` than
`f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  perfect-image-has-distinct-image :
    (a a₀ : A) → ¬ (is-perfect-image f g a) → (ρ : is-perfect-image f g a₀) →
    f a ≠ inverse-of-perfect-image a₀ ρ
  perfect-image-has-distinct-image a a₀ nρ ρ p =
    v ρ
    where
    q : g (f a) ＝ a₀
    q = ap g p ∙ is-section-inverse-of-perfect-image a₀ ρ

    s : ¬ (is-perfect-image f g (g (f a)))
    s = λ η → nρ (previous-perfect-image a η)

    v : ¬ (is-perfect-image f g a₀)
    v = tr (λ _ → ¬ (is-perfect-image f g _)) q s
```

Using the property above, we can talk about origins of `a` which are not images
of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-not-perfect-image : (a : A) → UU (l1 ⊔ l2)
  is-not-perfect-image a =
    Σ A (λ a₀ → (Σ ℕ (λ n → ((iterate n (g ∘ f)) a₀ ＝ a) × ¬ (fiber g a₀))))
```

If we assume the law of excluded middle and `g` is an embedding, we can prove
that if `is-not-perfect-image a` does not hold, we have `is-perfect-image a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (is-emb-g : is-emb g)
  (lem : LEM (l1 ⊔ l2))
  where

  is-perfect-not-not-is-perfect-image :
    (a : A) → ¬ (is-not-perfect-image a) → is-perfect-image f g a
  is-perfect-not-not-is-perfect-image a nρ a₀ n p =
    rec-coproduct
      ( id)
      ( λ a₁ → ex-falso (nρ (a₀ , n , p , a₁)))
      ( lem (fiber g a₀ , is-prop-map-is-emb is-emb-g a₀))
```

The following property states that if `g (b)` is not a perfect image, then `b`
has an `f` fiber `a` that is not a perfect image for `g`. Again, we need to
assume law of excluded middle and that both `g` and `f` are embedding.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A}
  (is-emb-f : is-emb f) (is-emb-g : is-emb g)
  (lem : LEM (l1 ⊔ l2))
  where

  not-perfect-image-has-not-perfect-fiber :
      (b : B) →
      ¬ (is-perfect-image f g (g b)) →
      Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
  not-perfect-image-has-not-perfect-fiber b nρ = v
      where
      i : ¬¬ (is-not-perfect-image {f = f} (g b))
      i = λ nμ → nρ (is-perfect-not-not-is-perfect-image is-emb-g lem (g b) nμ)

      ii :
        is-not-perfect-image (g b) →
        Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
      ii (x₀ , 0 , u) =
        ex-falso (pr2 u (b , inv (pr1 u)))
      ii (x₀ , succ-ℕ n , u) =
        a , w
        where
        q : f (iterate n (g ∘ f) x₀) ＝ b
        q = is-injective-is-emb is-emb-g (pr1 u)

        a : fiber f b
        a = iterate n (g ∘ f) x₀ , q

        w : ¬ (is-perfect-image f g ((iterate n (g ∘ f)) x₀))
        w = λ s → pr2 u (s x₀ n refl)

      iii : ¬¬ (Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s))))
      iii = λ t → i (λ s → t (ii s))

      iv : is-prop (Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s))))
      iv =
        is-prop-Σ
          (is-prop-map-is-emb is-emb-f b)
          (λ s → is-prop-neg {A = is-perfect-image f g (pr1 s)})

      v : Σ (fiber f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
      v = double-negation-elim-is-decidable (lem (_ , iv)) iii
```
