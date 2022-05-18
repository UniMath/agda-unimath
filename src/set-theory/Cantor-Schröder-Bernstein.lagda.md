# Cantor-Schröder-Bernstein

```agda
{-# OPTIONS --without-K --exact-split #-}

module set-theory.Cantor-Schröder-Bernstein where

open import elementary-number-theory.natural-numbers using
  (ℕ; zero-ℕ; succ-ℕ)
open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr; ind-coprod)
open import foundation.decidable-types using
  (is-decidable; dn-elim-is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.double-negation using (¬¬)
open import foundation.embeddings using (is-emb; _↪_)
open import foundation.empty-types using (ex-falso)
open import foundation.equivalences using (is-equiv; _≃_)
open import foundation.fibers-of-maps using(fib)
open import foundation.functions using (id; _∘_)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id; refl; inv; ap; _∙_; tr)
open import foundation.injective-maps using (is-injective; is-injective-is-emb)
open import foundation.law-of-excluded-middle using (LEM)
open import foundation.negation using (¬; is-prop-neg)
open import foundation.propositions using
  (is-prop; eq-is-prop'; is-prop-Π; is-prop-Σ)
open import foundation.propositional-maps using (is-prop-map-is-emb)
open import foundation.retractions using (retr)
open import foundation.sections using (sec)
open import foundation.split-surjective-maps using
  (is-split-surjective; is-equiv-is-split-surjective-is-injective)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

The classical Cantor–Schröder–Bernstein Theorem of set theory, formulated by Cantor and first proved by Bernstein, states that for any pair of sets `A` and `B`, if there are injective maps `f : A → B` and `g : B → A`, then one can find a bijection `h : A → B`. There are proofs that use the principle of excluded middle but not the axiom of choice. That the principle excluded middle is absolutely necessary.

Here, we will prove the following theorem assuming the terminology and notation of the HoTT book.

From given embeddings of two types into each other, we can construct an equivalence between them using the principle of excluded middle.

The idea and the proof is given by Martin Escardo in his paper ["The Cantor–Schröder–Bernstein Theorem for ∞-groupoids"](https://doi.org/10.1007/s40062-021-00284-6). Also, the proof is formalized in Agda ([Link 1](https://www.cs.bham.ac.uk/~mhe/TypeTopology/CantorSchroederBernstein.html), [Link 2](https://github.com/martinescardo/TypeTopology)). We will follow the same proof but using agda.unimath library notation.

### Preparation

For any map `f : A → A`, we can define its iterated compositions. It's needed due to define `is-g-point` notion in the proof.

```agda
_^_ :  {l1 : Level} {A : UU l1} → (A → A) → ℕ → (A → A)
f ^ zero-ℕ = id
f ^ succ-ℕ n = f ∘ (f ^ n)
```

### Proof

We will prove that LEM implies Cantor-Schröder-Bernstein.

```agda
Cantor-Schröder-Bernstein : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
Cantor-Schröder-Bernstein l1 l2 =
  {X : UU l1} {Y : UU l2} → ((X ↪ Y) × (Y ↪ X) → X ≃ Y)

LEM-implies-Cantor-Schröder-Bernstein :
  {l1 l2 : Level} →
  LEM (l1 ⊔ l2) →
  Cantor-Schröder-Bernstein l1 l2
LEM-implies-Cantor-Schröder-Bernstein {l1} {l2} lem {X} {Y}
  (pair (pair f is-emb-f) (pair g is-emb-g)) =
    pair h h-is-equiv
    where
    is-g-point : (x : X) →  UU (l1 ⊔ l2)
    is-g-point x = (x₀ : X) (n : ℕ) → Id (((g ∘ f) ^ n) x₀) x → fib g x₀

    is-prop-is-g-point : (x : X) → is-prop (is-g-point x)
    is-prop-is-g-point x =
      is-prop-Π (λ x₀ → (is-prop-Π λ n →
        is-prop-Π (λ p → (is-prop-map-is-emb is-emb-g x₀))))

    δ : (x : X) → is-decidable (is-g-point x)
    δ x = lem (pair (is-g-point x) (is-prop-is-g-point x))
   
    g-point-has-preimage : (x : X) → is-g-point x → fib g x
    g-point-has-preimage x ρ = ρ x 0 refl
   
    g⁻¹ : (x : X) → is-g-point x → Y
    g⁻¹ x ρ = pr1 (g-point-has-preimage x ρ)

    g⁻¹-is-sec-of-g : (x : X) (ρ : is-g-point x) → Id (g (g⁻¹ x ρ)) x
    g⁻¹-is-sec-of-g x ρ = pr2 (g-point-has-preimage x ρ) 

    g⁻¹-is-retr-of-g : (y : Y) (ρ : is-g-point (g y)) → Id (g⁻¹ (g y) ρ) y
    g⁻¹-is-retr-of-g y ρ =
      is-injective-is-emb is-emb-g (g⁻¹-is-sec-of-g (g y) ρ)
```

The next function will be the bijection we want.

```agda
    h : X → Y
    h x = ind-coprod _ (g⁻¹ x) (λ t → f x) (δ x)

    α : (x : X) → is-g-point (g (f x)) → is-g-point x
    α x ρ x₀ n p = ρ x₀ (succ-ℕ n) (ap (g ∘ f) p)

    f-and-g⁻¹-have-disjoint-images : (x x' : X) →
                                     ¬ (is-g-point x) →
                                     (ρ : is-g-point x') →
                                     ¬ (Id (f x) (g⁻¹ x' ρ))
    f-and-g⁻¹-have-disjoint-images x x' nρ ρ p = v ρ
      where
      q : Id (g (f x)) x'
      q = ap g p ∙ g⁻¹-is-sec-of-g x' ρ

      s : ¬ (is-g-point (g (f x)))
      s = λ η → nρ (α x η)

      v : ¬ (is-g-point x')
      v = tr (λ _ → ¬ (is-g-point _)) q s
```

It is convenient to work with the following auxiliary function `H` and prove properties of `H` and then specialize them to `h`:

```agda
    H : (x : X) → is-decidable (is-g-point x) → Y
    H x d = ind-coprod _ (g⁻¹ x) (λ t → f x) d
```

By definition, `H` and `h` are the same function. Wel'll prove `h` is injective split surjection using `H`.

```agda
    h=H : Id h (λ x → H x (δ x))
    h=H = refl

    is-injective-h : is-injective h
    is-injective-h {x} {x'} = l (δ x) (δ x')
      where
      l :
        (d : is-decidable (is-g-point x))
        (d' : is-decidable (is-g-point x')) →
        Id (H x d) (H x' d') → Id x x'
      l (inl ρ) (inl ρ') p =
        inv (g⁻¹-is-sec-of-g x ρ) ∙ (ap g p ∙ g⁻¹-is-sec-of-g x' ρ')
      l (inl ρ) (inr nρ') p =
        ex-falso (f-and-g⁻¹-have-disjoint-images x' x nρ' ρ (inv p))
      l (inr nρ) (inl ρ') p =
        ex-falso ((f-and-g⁻¹-have-disjoint-images x x' nρ ρ' p))
      l (inr nρ) (inr nρ') p =
        is-injective-is-emb is-emb-f p

    f-point : (x : X) → UU (l1 ⊔ l2)
    f-point x =
      Σ X (λ x₀ → (Σ ℕ (λ n →  (Id (((g ∘ f) ^ n) x₀) x) × ¬ (fib g x₀))))

    non-f-point-is-g-point : (x : X) → ¬ (f-point x) → (is-g-point x)
    non-f-point-is-g-point x nρ x₀ n p =
       ind-coprod _
         (id)
         (λ x₁ → ex-falso (nρ (pair x₀ (pair n (pair p x₁)))))
         (lem (pair (fib g x₀) (is-prop-map-is-emb is-emb-g x₀)))
```

The following claim states that if `g (y)` is not a `g-point`, then there is a designated point `(x : X , p : f(x)=y)` of the `f`-fiber of `y` such that `x` is not a `g-point` either. The claim is used to show `h` is split surjective.

```agda
    claim :
      (y : Y) →
      ¬ (is-g-point (g y)) →
      Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s)))
    claim y nρ = v
      where
      i : ¬¬ (f-point (g y))
      i = λ nμ → nρ (non-f-point-is-g-point (g y) nμ)

      ii : f-point (g y) → Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s)))
      ii (pair x₀ (pair zero-ℕ u)) = ex-falso (pr2 u (pair y (inv (pr1 u))))
      ii (pair x₀ (pair (succ-ℕ n) u)) = pair a b
        where
        q : Id (f (((g ∘ f) ^ n) x₀)) y
        q = is-injective-is-emb is-emb-g (pr1 u)

        a : fib f y
        a = pair (((g ∘ f) ^ n) x₀)  q

        b : ¬ (is-g-point (((g ∘ f) ^ n) x₀))
        b = λ s → pr2 u (s x₀ n refl)

      iii : ¬¬ (Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s))))
      iii = λ t → i (λ s → t (ii s))

      iv : is-prop (Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s))))
      iv =
        is-prop-Σ
          (is-prop-map-is-emb is-emb-f y)
          (λ s → is-prop-neg {A = is-g-point (pr1 s)})

      v : Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s)))
      v = dn-elim-is-decidable _ (lem (pair _ iv)) iii

    is-split-surjective-h : is-split-surjective h
    is-split-surjective-h y = pair x p
      where
      a :
        is-decidable (is-g-point (g y)) →
        Σ X (λ x → ((d : is-decidable (is-g-point x)) → Id (H x d) y))
      a (inl γ) = pair (g y) ψ
        where
        ψ : (d : is-decidable (is-g-point (g y))) → Id (H (g y) d) y
        ψ (inl v') = g⁻¹-is-retr-of-g y v'
        ψ (inr v)  = ex-falso (v γ)
      a (inr γ) = pair x ψ
        where
        w : Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s)))
        w = claim y γ

        x : X
        x = pr1 (pr1 w)

        p : Id (f x) y
        p = pr2 (pr1 w)

        ψ : (d : is-decidable (is-g-point x)) → Id (H x d) y
        ψ (inl v) = ex-falso ((pr2 w) v)
        ψ (inr v) = p

      b : Σ X (λ x → ((d : is-decidable (is-g-point x)) → Id (H x d) y))
      b = a (δ (g y))

      x : X
      x = pr1 b

      p : Id (h x) y
      p = pr2 b (δ x)

    h-is-equiv : is-equiv h
    h-is-equiv =
      is-equiv-is-split-surjective-is-injective
        h
        is-injective-h
        is-split-surjective-h      
```
