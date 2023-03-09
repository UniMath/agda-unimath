# Perfect Images

```agda
module foundation.perfect-images where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.embeddings
open import foundation.empty-types
open import foundation.fibers-of-maps
open import foundation.functions
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.iterating-functions
open import foundation.law-of-excluded-middle
open import foundation.negation
open import foundation.propositional-maps
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Consider two maps `f : A → B` and `g : B → A`. For `(g ◦ f ) ^ n (a₀) = a`, consider also the following chain

  `a₀ --> f (a₀) --> g (f (a₀)) --> f (g (f (a₀))) --> ... --> (g ◦ f ) ^ n (a₀) = a`

We say `a₀` is an origin for `a`, and  `a` is `perfect image` for `g` if any origin of `a` is in the image of `g`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (g : B → A)
  where

  is-perfect-image : (a : A) →  UU (l1 ⊔ l2)
  is-perfect-image a =
    (a₀ : A) (n : ℕ) → (iterate n (g ∘ f)) a₀ ＝ a → fib g a₀
```

## Properties

If `g` is an embedding, then `is-perfect-image a` is a proposition. In this case, if we assume law of exluded middle, we can show `is-perfect-image a` is a decidable type for any `a : A`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (is-emb-g : is-emb g)
  where

  is-prop-is-perfect-image-is-emb :
    (a : A) → is-prop (is-perfect-image f g a)
  is-prop-is-perfect-image-is-emb a =
     is-prop-Π (λ a₀ → (is-prop-Π λ n →
        is-prop-Π (λ p → (is-prop-map-is-emb is-emb-g a₀))))

  is-perfect-image-Prop : A → Prop (l1 ⊔ l2)
  pr1 (is-perfect-image-Prop a) = is-perfect-image f g a
  pr2 (is-perfect-image-Prop a) = is-prop-is-perfect-image-is-emb a

  is-decidable-is-perfect-image-is-emb :
    LEM (l1 ⊔ l2) → (a : A) → is-decidable (is-perfect-image f g a)
  is-decidable-is-perfect-image-is-emb lem a =
    lem (is-perfect-image-Prop a)
```

If `a` is a perfect image for `g`, then `a` has a preimage under `g`. Just take n=zero in the definition.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-perfect-image-is-fib :
    {f : A → B} {g : B → A} → (a : A) →
    is-perfect-image f g a → fib g a
  is-perfect-image-is-fib a ρ = ρ a 0 refl
```

One can define a map from `A` to `B` restricting the domain to the perfect images of `g`. This gives a kind of section of g. When g is also an embedding, the map gives a kind of retraction of g.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  inverse-of-perfect-image :
    (a : A) → (is-perfect-image f g a) → B
  inverse-of-perfect-image a ρ =
    pr1 (is-perfect-image-is-fib a ρ)

  is-sec-inverse-of-perfect-image :
    (a : A) (ρ : is-perfect-image f g a) →
    g (inverse-of-perfect-image a ρ) ＝ a
  is-sec-inverse-of-perfect-image a ρ =
    pr2 (is-perfect-image-is-fib a ρ)
```

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} {is-emb-g : is-emb g}
  where

  is-retr-inverse-of-perfect-image :
    (b : B) (ρ : is-perfect-image f g (g b)) →
    inverse-of-perfect-image (g b) ρ ＝ b
  is-retr-inverse-of-perfect-image b ρ =
     is-injective-is-emb
       is-emb-g
       (is-sec-inverse-of-perfect-image (g b) ρ)
```

If `g (f (a))` is a perfect image for `g`, so is `a`.

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

Perfect images goes to a disjoint place under `inverse-of-perfect-image` than `f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  perfect-image-has-distinct-image :
    (a a₀ : A) → ¬ (is-perfect-image f g a) → (ρ : is-perfect-image f g a₀) →
    ¬ (f a ＝ inverse-of-perfect-image a₀ ρ)
  perfect-image-has-distinct-image a a₀ nρ ρ p = v ρ
    where
    q : g (f a) ＝ a₀
    q = ap g p ∙ is-sec-inverse-of-perfect-image a₀ ρ

    s : ¬ (is-perfect-image f g (g (f a)))
    s = λ η → nρ (previous-perfect-image a η)

    v : ¬ (is-perfect-image f g a₀)
    v = tr (λ _ → ¬ (is-perfect-image f g _)) q s
```

Using the property above, we can talk about origins of `a` which are not images of `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} {g : B → A}
  where

  is-not-perfect-image : (a : A) → UU (l1 ⊔ l2)
  is-not-perfect-image a =
    Σ A (λ a₀ → (Σ ℕ (λ n →  ((iterate n (g ∘ f)) a₀ ＝ a) × ¬ (fib g a₀))))
```

If we assume law of excluded middle and `g` is embedding, we can prove that if `is-not-perfect-image a` does not hold, we have `is-perfect-image a`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f : A → B} {g : B → A} (is-emb-g : is-emb g)
  (lem : LEM (l1 ⊔ l2))
  where

  not-not-perfect-is-perfect :
    (a : A) →
    ¬ (is-not-perfect-image a) →
    (is-perfect-image f g a)
  not-not-perfect-is-perfect a nρ a₀ n p =
    ind-coprod _
      (id)
      (λ a₁ → ex-falso (nρ (pair a₀ (pair n (pair p a₁)))))
      (lem (pair (fib g a₀) (is-prop-map-is-emb is-emb-g a₀)))
```

The following property states that if `g (b)` is not a perfect image, then `b` has an `f` fiber `a` that is not a perfect image for `g`. Again, we need to assume law of excluded middle and that both `g` and `f` are embedding.

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
      Σ (fib f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
  not-perfect-image-has-not-perfect-fiber b nρ = v
      where
      i : ¬¬ (is-not-perfect-image {f = f} (g b))
      i = λ nμ → nρ (not-not-perfect-is-perfect is-emb-g lem (g b) nμ)

      ii :
        is-not-perfect-image (g b) →
        Σ (fib f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
      ii (pair x₀ (pair zero-ℕ u)) =
        ex-falso (pr2 u (pair b (inv (pr1 u))))
      ii (pair x₀ (pair (succ-ℕ n) u)) = pair a w
        where
        q : f ((iterate n (g ∘ f)) x₀) ＝ b
        q = is-injective-is-emb is-emb-g (pr1 u)

        a : fib f b
        a = pair ((iterate n (g ∘ f)) x₀)  q

        w : ¬ (is-perfect-image f g ((iterate n (g ∘ f)) x₀))
        w = λ s → pr2 u (s x₀ n refl)

      iii : ¬¬ (Σ (fib f b) (λ s → ¬ (is-perfect-image f g (pr1 s))))
      iii = λ t → i (λ s → t (ii s))

      iv : is-prop (Σ (fib f b) (λ s → ¬ (is-perfect-image f g (pr1 s))))
      iv =
        is-prop-Σ
          (is-prop-map-is-emb is-emb-f b)
          (λ s → is-prop-neg {A = is-perfect-image f g (pr1 s)})

      v : Σ (fib f b) (λ s → ¬ (is-perfect-image f g (pr1 s)))
      v = dn-elim-is-decidable (lem (pair _ iv)) iii
```
