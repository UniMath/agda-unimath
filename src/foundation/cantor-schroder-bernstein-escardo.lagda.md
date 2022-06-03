---
title: Cantor-Schröder-Bernstein
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.cantor-schroder-bernstein-escardo where

open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr; ind-coprod)
open import foundation.decidable-types using (is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.empty-types using (ex-falso)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.fibers-of-maps using(fib)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; inv; ap; _∙_)
open import foundation.injective-maps using (is-injective; is-injective-is-emb)
open import foundation.law-of-excluded-middle using (LEM)
open import foundation.negation using (¬)
open import foundation.perfect-images
open import foundation.split-surjective-maps using
  (is-split-surjective; is-equiv-is-split-surjective-is-injective)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

The classical Cantor-Schröder-Bernstein theorem asserts that from any pair of injective maps `f : A → B` and `g : B → A` we can construct a bijection between `A` and `B`. In a recent generalization [1], Escardó proved that the Cantor-Schröder-Bernstein theorem also holds for ∞-groupoids. His generalization asserts that from given embeddings of two types into each other, we can construct an equivalence between them.

## Statement

```agda
cantor-schroder-bernstein : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
cantor-schroder-bernstein l1 l2 =
  {X : UU l1} {Y : UU l2} → ((X ↪ Y) × (Y ↪ X) → X ≃ Y)
```

## Proof

We will prove that LEM implies Cantor-Schröder-Bernstein.

```agda
LEM-implies-cantor-schroder-bernstein :
  {l1 l2 : Level} →
  LEM (l1 ⊔ l2) →
  cantor-schroder-bernstein l1 l2
LEM-implies-cantor-schroder-bernstein {l1} {l2} lem {X} {Y}
  (pair (pair f is-emb-f) (pair g is-emb-g)) =
    pair h h-is-equiv
```

Below, we will define `h` and the proof `h-is-equiv` that says `h` is an equivalence.

```agda
    where
    h : X → Y
    h x =
      ind-coprod _
      (inverse-of-perfect-image {f = f} x)
      (λ t → f x)
      (is-emb-is-decidable-is-perfect-image is-emb-g lem x)
```

It is convenient to work with the following auxiliary function `H` and prove properties of `H` and then specialize them to `h`:

```agda
    H : (x : X) → is-decidable (is-perfect-image f g x) → Y
    H x d = ind-coprod _ (inverse-of-perfect-image x) (λ t → f x) d

    is-injective-h : is-injective h
    is-injective-h {x} {x'} =
      l (is-emb-is-decidable-is-perfect-image is-emb-g lem x)
        (is-emb-is-decidable-is-perfect-image is-emb-g lem x')
      where
      l :
        (d : is-decidable (is-perfect-image f g x))
        (d' : is-decidable (is-perfect-image f g x')) →
        Id (H x d) (H x' d') → Id x x'
      l (inl ρ) (inl ρ') p =
        inv (is-sec-inverse-of-perfect-image x ρ) ∙
          (ap g p ∙ is-sec-inverse-of-perfect-image x' ρ')
      l (inl ρ) (inr nρ') p =
        ex-falso (perfect-image-has-distinct-image x' x nρ' ρ (inv p))
      l (inr nρ) (inl ρ') p =
        ex-falso (perfect-image-has-distinct-image x x' nρ ρ' p)
      l (inr nρ) (inr nρ') p =
        is-injective-is-emb is-emb-f p

    is-split-surjective-h : is-split-surjective h
    is-split-surjective-h y = pair x p
      where
      a :
        is-decidable (is-perfect-image f g (g y)) →
        Σ X (λ x → ((d : is-decidable (is-perfect-image f g x)) → Id (H x d) y))
      a (inl γ) = pair (g y) ψ
        where
        ψ : (d : is-decidable (is-perfect-image f g (g y))) → Id (H (g y) d) y
        ψ (inl v') = is-retr-inverse-of-perfect-image {is-emb-g = is-emb-g} y v'
        ψ (inr v)  = ex-falso (v γ)
      a (inr γ) = pair x ψ
        where
        w : Σ (fib f y) (λ s → ¬ (is-perfect-image f g (pr1 s)))
        w = not-perfect-image-has-not-perfect-fiber is-emb-f is-emb-g lem y γ

        x : X
        x = pr1 (pr1 w)

        p : Id (f x) y
        p = pr2 (pr1 w)

        ψ : (d : is-decidable (is-perfect-image f g x)) → Id (H x d) y
        ψ (inl v) = ex-falso ((pr2 w) v)
        ψ (inr v) = p

      b :
        Σ X
          (λ x → ((d : is-decidable (is-perfect-image f g x)) → Id (H x d) y))
      b = a (is-emb-is-decidable-is-perfect-image is-emb-g lem (g y))

      x : X
      x = pr1 b

      p : Id (h x) y
      p = pr2 b (is-emb-is-decidable-is-perfect-image is-emb-g lem x)

    h-is-equiv : is-equiv h
    h-is-equiv =
      is-equiv-is-split-surjective-is-injective
        h
        is-injective-h
        is-split-surjective-h
```

## References

[1] The idea and the proof is given by Martin Escardo in his paper ["The Cantor–Schröder–Bernstein Theorem for ∞-groupoids"](https://doi.org/10.1007/s40062-021-00284-6). Also, the proof is formalized in Agda ([Link 1](https://www.cs.bham.ac.uk/~mhe/TypeTopology/CantorSchroederBernstein.html), [Link 2](https://github.com/martinescardo/TypeTopology)). 
