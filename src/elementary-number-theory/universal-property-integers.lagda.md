# The universal property of the integers

```agda
module elementary-number-theory.universal-property-integers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
```

</details>

## Idea

The universal property of [the integers](elementary-number-theory.integers.md)
states that given any type `X` equipped with a point `x : X` and an
[automorphism](foundation.automorphisms.md) `e : X ≃ X`, there is a
[unique](foundation.contractible-types.md) structure preserving map from `ℤ` to
`X`.

```agda
abstract
  elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( k : ℤ) → P k
  elim-ℤ P p0 pS (inl zero-ℕ) =
    map-inv-is-equiv (is-equiv-map-equiv (pS neg-one-ℤ)) p0
  elim-ℤ P p0 pS (inl (succ-ℕ x)) =
    map-inv-is-equiv
      ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
      ( elim-ℤ P p0 pS (inl x))
  elim-ℤ P p0 pS (inr (inl _)) = p0
  elim-ℤ P p0 pS (inr (inr zero-ℕ)) = map-equiv (pS zero-ℤ) p0
  elim-ℤ P p0 pS (inr (inr (succ-ℕ x))) =
    map-equiv
      ( pS (inr (inr x)))
      ( elim-ℤ P p0 pS (inr (inr x)))

  compute-zero-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    elim-ℤ P p0 pS zero-ℤ ＝ p0
  compute-zero-elim-ℤ P p0 pS = refl

  compute-succ-elim-ℤ :
    { l1 : Level} (P : ℤ → UU l1)
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) (k : ℤ) →
    Id (elim-ℤ P p0 pS (succ-ℤ k)) (map-equiv (pS k) (elim-ℤ P p0 pS k))
  compute-succ-elim-ℤ P p0 pS (inl zero-ℕ) =
    inv
      ( is-section-map-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl zero-ℕ)))
        ( elim-ℤ P p0 pS (succ-ℤ (inl zero-ℕ))))
  compute-succ-elim-ℤ P p0 pS (inl (succ-ℕ x)) =
    inv
      ( is-section-map-inv-is-equiv
        ( is-equiv-map-equiv (pS (inl (succ-ℕ x))))
        ( elim-ℤ P p0 pS (succ-ℤ (inl (succ-ℕ x)))))
  compute-succ-elim-ℤ P p0 pS (inr (inl _)) = refl
  compute-succ-elim-ℤ P p0 pS (inr (inr _)) = refl

ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → UU l1
ELIM-ℤ P p0 pS =
  Σ ( (k : ℤ) → P k)
    ( λ f →
      ( ( f zero-ℤ ＝ p0) ×
        ( (k : ℤ) → Id (f (succ-ℤ k)) ((map-equiv (pS k)) (f k)))))

Elim-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) → ELIM-ℤ P p0 pS
pr1 (Elim-ℤ P p0 pS) = elim-ℤ P p0 pS
pr1 (pr2 (Elim-ℤ P p0 pS)) = compute-zero-elim-ℤ P p0 pS
pr2 (pr2 (Elim-ℤ P p0 pS)) = compute-succ-elim-ℤ P p0 pS

equiv-comparison-map-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (k : ℤ) →
  (pr1 s k ＝ pr1 t k) ≃ (pr1 s (succ-ℤ k) ＝ pr1 t (succ-ℤ k))
equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t k =
  ( ( equiv-concat (pr2 (pr2 s) k) (pr1 t (succ-ℤ k))) ∘e
    ( equiv-concat' (map-equiv (pS k) (pr1 s k)) (inv (pr2 (pr2 t) k)))) ∘e
  ( equiv-ap (pS k) (pr1 s k) (pr1 t k))

zero-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
zero-Eq-ELIM-ℤ P p0 pS s t H =
  (H zero-ℤ ＝ pr1 (pr2 s) ∙ inv (pr1 (pr2 t)))

succ-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) (H : (pr1 s) ~ (pr1 t)) → UU l1
succ-Eq-ELIM-ℤ P p0 pS s t H =
  ( k : ℤ) →
  Id
    ( H (succ-ℤ k))
    ( map-equiv (equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t k) (H k))

Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → UU l1
Eq-ELIM-ℤ P p0 pS s t =
  ELIM-ℤ
    ( λ k → pr1 s k ＝ pr1 t k)
    ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
    ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)

reflexive-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1)
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s s
pr1 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H)) = refl-htpy
pr1 (pr2 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H))) = inv (right-inv p)
pr2 (pr2 (reflexive-Eq-ELIM-ℤ P p0 pS (f , p , H))) = inv ∘ (right-inv ∘ H)

Eq-ELIM-ℤ-eq :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → s ＝ t → Eq-ELIM-ℤ P p0 pS s t
Eq-ELIM-ℤ-eq P p0 pS s .s refl = reflexive-Eq-ELIM-ℤ P p0 pS s

abstract
  is-torsorial-Eq-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s : ELIM-ℤ P p0 pS) → is-torsorial (Eq-ELIM-ℤ P p0 pS s)
  is-torsorial-Eq-ELIM-ℤ P p0 pS s =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (pr1 s))
      ( pair (pr1 s) refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-contr-is-equiv'
          ( Σ (pr1 s zero-ℤ ＝ p0) (λ α → Id α (pr1 (pr2 s))))
          ( tot (λ α → right-transpose-eq-concat refl α (pr1 (pr2 s))))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ α → is-equiv-right-transpose-eq-concat refl α (pr1 (pr2 s))))
          ( is-torsorial-Id' (pr1 (pr2 s))))
        ( pair (pr1 (pr2 s)) (inv (right-inv (pr1 (pr2 s)))))
        ( is-contr-is-equiv'
          ( Σ ( ( k : ℤ) → Id (pr1 s (succ-ℤ k)) (pr1 (pS k) (pr1 s k)))
              ( λ β → β ~ (pr2 (pr2 s))))
          ( tot (λ β → right-transpose-htpy-concat refl-htpy β (pr2 (pr2 s))))
          ( is-equiv-tot-is-fiberwise-equiv
            ( λ β →
              is-equiv-right-transpose-htpy-concat refl-htpy β (pr2 (pr2 s))))
          ( is-torsorial-htpy' (pr2 (pr2 s)))))

abstract
  is-equiv-Eq-ELIM-ℤ-eq :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    ( s t : ELIM-ℤ P p0 pS) → is-equiv (Eq-ELIM-ℤ-eq P p0 pS s t)
  is-equiv-Eq-ELIM-ℤ-eq P p0 pS s =
    fundamental-theorem-id
      ( is-torsorial-Eq-ELIM-ℤ P p0 pS s)
      ( Eq-ELIM-ℤ-eq P p0 pS s)

eq-Eq-ELIM-ℤ :
  { l1 : Level} (P : ℤ → UU l1) →
  ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
  ( s t : ELIM-ℤ P p0 pS) → Eq-ELIM-ℤ P p0 pS s t → s ＝ t
eq-Eq-ELIM-ℤ P p0 pS s t = map-inv-is-equiv (is-equiv-Eq-ELIM-ℤ-eq P p0 pS s t)

abstract
  is-prop-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-prop (ELIM-ℤ P p0 pS)
  is-prop-ELIM-ℤ P p0 pS =
    is-prop-all-elements-equal
      ( λ s t → eq-Eq-ELIM-ℤ P p0 pS s t
        ( Elim-ℤ
          ( λ k → pr1 s k ＝ pr1 t k)
          ( (pr1 (pr2 s)) ∙ (inv (pr1 (pr2 t))))
          ( equiv-comparison-map-Eq-ELIM-ℤ P p0 pS s t)))
```

### The dependent universal property of the integers

```agda
abstract
  is-contr-ELIM-ℤ :
    { l1 : Level} (P : ℤ → UU l1) →
    ( p0 : P zero-ℤ) (pS : (k : ℤ) → (P k) ≃ (P (succ-ℤ k))) →
    is-contr (ELIM-ℤ P p0 pS)
  is-contr-ELIM-ℤ P p0 pS =
    is-proof-irrelevant-is-prop (is-prop-ELIM-ℤ P p0 pS) (Elim-ℤ P p0 pS)
```

### The universal property of the integers

The nondependent universal property of the integers is a special case of the
dependent universal property applied to constant type families.

```agda
ELIM-ℤ' :
  { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → UU l1
ELIM-ℤ' {X = X} x e = ELIM-ℤ (λ k → X) x (λ k → e)

abstract
  universal-property-ℤ :
    { l1 : Level} {X : UU l1} (x : X) (e : X ≃ X) → is-contr (ELIM-ℤ' x e)
  universal-property-ℤ {X = X} x e = is-contr-ELIM-ℤ (λ k → X) x (λ k → e)
```
