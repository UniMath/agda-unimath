# Cantor-Schröder-Bernstein

```agda
{-# OPTIONS --without-K --exact-split #-}

module Cantor-Schröder-Bernstein where

open import elementary-number-theory.natural-numbers using (ℕ; zero-ℕ; succ-ℕ)
open import foundation.cartesian-product-types using (_×_)
open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using (is-decidable; dn-elim-is-decidable)
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
open import foundation.propositions using (is-prop; eq-is-prop'; is-prop-Π; is-prop-Σ)
open import foundation.propositional-maps using (is-prop-map-is-emb)
open import foundation.split-surjective-maps using (is-split-surjective)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```
## Idea

The classical Cantor–Schröder–Bernstein Theorem of set theory, formulated by Cantor and first proved by Bernstein, states that for any pair of sets A and B, if there are injective maps f : A → B and g : B → A, then one can find a bijection h : A → B. There are proofs that use the principle of excluded middle but not the axiom of choice. That the principle excluded middle is absolutely necessary.

Here, we will prove the following theorem assuming the terminology and notation of the HoTT book.

From given embeddings of two types into each other, we can construct an equivalence between them using the principle of excluded middle.

The idea and the proof is given by Martin Escardo in his paper "The Cantor–Schröder–Bernstein Theorem for ∞-groupoids". We will follow its proof using agda.unimath library settings.

Link : https://doi.org/10.1007/s40062-021-00284-6


###Preparation

For any map f : A → A, we can define its iterated compositions. It's needed due to define `is-g-point` notion in the proof.
```agda
_^_ : {l1 : Level} {A : UU l1}
      → (A → A) → ℕ
      → (A → A)
f ^ zero-ℕ = id
f ^ succ-ℕ n = f ∘ (f ^ n)
```

We also need an non-dependent version of induction principle for coproduct types

```agda
non-dep-ind-coprod : {l1 l2 l3 : Level} {A : UU l1} {B : UU l2 } {C : UU l3} → (A → C) → (B → C) → (coprod A B → C)
non-dep-ind-coprod f g (inl x) = f x
non-dep-ind-coprod f g (inr y) = g y
```

It's useful to prove that any injective split-surjection is an equivalence.

```agda
injective-split-surjections-are-equivs : {l1 l2 : Level} {X : UU l1} {Y : UU l2 } (f : X → Y)
                               → is-injective f
                               → is-split-surjective f
                               → is-equiv f
injective-split-surjections-are-equivs {X = X} {Y = Y}  f l s = pair (pair g ε) (pair g η) 
 where
  g : Y → X
  g y = pr1 (s y)

  ε : (f ∘ g) ~ id
  ε y = pr2 (s y)

  η : (g ∘ f) ~ id
  η x = l p
   where
    p : Id (f (g (f x))) (f x)
    p = ε (f x)
```
###Proof
We will prove that LEM implies Cantor-Schröder-Bernstein.

```agda
Cantor-Schröder-Bernstein : (l1 l2 : Level) → UU (lsuc (l1 ⊔ l2))
Cantor-Schröder-Bernstein l1 l2 = {X : UU l1} {Y : UU l2} → ((X ↪ Y) × (Y ↪ X) → X ≃ Y)


LEM-gives-Cantor-Schröder-Bernstein : {l1 l2 : Level}
                                   → LEM (l1 ⊔ l2)
                                   → Cantor-Schröder-Bernstein l1 l2
LEM-gives-Cantor-Schröder-Bernstein {l1} {l2} lem {X} {Y} (pair (pair f f-is-emb) (pair g g-is-emb)) = pair h h-is-equiv
  where
   is-g-point : (x : X) →  UU (l1 ⊔ l2)
   is-g-point x = (x₀ : X) (n : ℕ) → Id (((g ∘ f) ^ n) x₀) x → fib g x₀

   being-g-point-is-prop : (x : X) → is-prop (is-g-point x)
   being-g-point-is-prop x = is-prop-Π (λ x₀ →
                                       (is-prop-Π λ n →
                                                  is-prop-Π (λ p →
                                                            (is-prop-map-is-emb g-is-emb x₀))))

   
   g-is-invertible-at-g-points : (x : X) → is-g-point x → fib g x
   g-is-invertible-at-g-points x ρ = ρ x 0 refl
   
   g⁻¹ : (x : X) → is-g-point x → Y
   g⁻¹ x ρ = pr1 (g-is-invertible-at-g-points x ρ)

   δ : (x : X) → is-decidable (is-g-point x)
   δ x = lem (pair (is-g-point x) (being-g-point-is-prop x))
```
The next function will be the bijection we want.

```agda
   h : X → Y
   h x = non-dep-ind-coprod (g⁻¹ x) (λ t → f x) (δ x)

   g⁻¹-is-right-inv : (x : X) (ρ : is-g-point x) → Id (g (g⁻¹ x ρ)) x
   g⁻¹-is-right-inv x ρ = pr2 (g-is-invertible-at-g-points x ρ) 

   g⁻¹-is-left-inv : (y : Y) (ρ : is-g-point (g y)) → Id (g⁻¹ (g y) ρ) y
   g⁻¹-is-left-inv y ρ = is-injective-is-emb g-is-emb {g⁻¹ (g y) ρ} {y} (g⁻¹-is-right-inv (g y) ρ)

   α : (x : X) → is-g-point (g (f x)) → is-g-point x
   α x ρ x₀ n p = ρ x₀ (succ-ℕ n) (ap (g ∘ f) p)

   f-g⁻¹-disjoint-images : (x x' : X)
                        → ¬ (is-g-point x)
                        → (ρ : is-g-point x')
                        → ¬ (Id (f x) (g⁻¹ x' ρ))
   f-g⁻¹-disjoint-images x x' nρ ρ p = v ρ
     where
      q : Id (g (f x)) x'
      q = ap g p ∙ g⁻¹-is-right-inv x' ρ

      s : ¬ (is-g-point (g (f x)))
      s = λ η → nρ (α x η)

      v : ¬ (is-g-point x')
      v = tr (λ _ → ¬ (is-g-point _)) q s
```

It is convenient to work with the following auxiliary function H and prove properties of H and then specialize them to h:

```agda
   H : (x : X) → is-decidable (is-g-point x) → Y
   H x d = non-dep-ind-coprod (g⁻¹ x) (λ t → f x) d

   notice-that : Id h (λ x → H x (δ x))
   notice-that = refl

   h-is-injective : is-injective h
   h-is-injective {x} {x'} = l (δ x) (δ x')
    where
     l : (d : is-decidable (is-g-point x)) (d' : is-decidable (is-g-point x')) → Id (H x d) (H x' d') → Id x x'
     l (inl ρ) (inl ρ') p = inv (g⁻¹-is-right-inv x ρ) ∙ (ap g p ∙ g⁻¹-is-right-inv x' ρ')
     l (inl ρ) (inr nρ') p = ex-falso (f-g⁻¹-disjoint-images x' x nρ' ρ (inv p))
     l (inr nρ) (inl ρ') p = ex-falso ((f-g⁻¹-disjoint-images x x' nρ ρ' p))
     l (inr ρ) (inr ρ') p = is-injective-is-emb f-is-emb p

   f-point : (x : X) → UU (l1 ⊔ l2)
   f-point x = Σ X  (λ x₀ → (Σ ℕ (λ n →  (Id (((g ∘ f) ^ n) x₀) x) × ¬ (fib g x₀))))

   non-f-point-is-g-point : (x : X) → ¬ (f-point x) → (is-g-point x)
   non-f-point-is-g-point x nρ x₀ n p =
      non-dep-ind-coprod (id) (λ x₁ → ex-falso (nρ (pair x₀ (pair n (pair p x₁))) ))
                         (lem (pair (fib g x₀) (is-prop-map-is-emb g-is-emb x₀)))

   claim : (y : Y) → ¬ (is-g-point (g y)) → Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s)))
   claim y nρ = v
    where
     i : ¬¬ (f-point (g y))
     i = λ nμ → nρ (non-f-point-is-g-point (g y) nμ)

     ii : f-point (g y) → Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s)))
     ii (pair x₀ (pair zero-ℕ u)) = ex-falso (pr2 u (pair y (inv (pr1 u))))
     ii (pair x₀ (pair (succ-ℕ n) u)) = pair a b
       where
       q : Id (f (((g ∘ f) ^ n) x₀)) y
       q = is-injective-is-emb g-is-emb (pr1 u)

       a : fib f y
       a = pair (((g ∘ f) ^ n) x₀)  q

       b : ¬ (is-g-point (((g ∘ f) ^ n) x₀))
       b = λ s → pr2 u (s x₀ n refl)

     iii : ¬¬ (Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s))))
     iii = λ t → i (λ s → t (ii s))

     iv : is-prop (Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s))))
     iv = is-prop-Σ (is-prop-map-is-emb f-is-emb y) λ s → is-prop-neg {A = is-g-point (pr1 s)}

     v : Σ (fib f y) (λ s → ¬ (is-g-point (pr1 s)))
     v = dn-elim-is-decidable _ (lem (pair _ iv)) iii

   h-is-split-surjective : is-split-surjective h
   h-is-split-surjective y = pair x p
    where
     a : is-decidable (is-g-point (g y)) → Σ X (λ x → ((d : is-decidable (is-g-point x)) → Id (H x d) y))
     a (inl γ) = pair (g y) ψ
      where
       ψ : (d : is-decidable (is-g-point (g y))) → Id (H (g y) d) y
       ψ (inl v') = g⁻¹-is-left-inv y v'
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
   h-is-equiv = injective-split-surjections-are-equivs h h-is-injective h-is-split-surjective
      
```
