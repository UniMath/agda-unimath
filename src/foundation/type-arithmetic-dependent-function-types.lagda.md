# Type arithmetic with dependent function types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.type-arithmetic-dependent-function-types where

open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; is-contr-total-path)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (equiv-ap)
open import foundation.equality-dependent-pair-types using (eq-pair-Σ)
open import foundation.equivalences using
  ( is-equiv; map-inv-equiv; is-equiv-has-inverse; _≃_; map-inv-is-equiv; _∘e_)
open import foundation.function-extensionality using
  ( is-contr-total-htpy; eq-htpy; equiv-funext)
open import foundation.functions using (_∘_; id)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using (refl-htpy; _~_)
open import foundation.identity-types using (Id; refl; tr)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure; extensionality-Σ)
open import foundation.universe-levels using (Level; UU; _⊔_)
open import foundation.weak-function-extensionality using (is-contr-Π)
```

## Idea

We prove arithmetical laws involving dependent function types.

## Laws

### Distributivity of Π over Σ

```agda
Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
Π-total-fam {A = A} {B} C = (x : A) → Σ (B x) (C x)

universally-structured-Π :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (C : (x : A) → B x → UU l3) → UU (l1 ⊔ (l2 ⊔ l3))
universally-structured-Π {A = A} {B} C =
  Σ ((x : A) → B x) (λ f → (x : A) → C x (f x))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  where
  
  htpy-universally-structured-Π :
    (t t' : universally-structured-Π C) → UU (l1 ⊔ (l2 ⊔ l3))
  htpy-universally-structured-Π t t' =
    universally-structured-Π
      ( λ (x : A) (p : Id ((pr1 t) x) ((pr1 t') x)) →
        Id (tr (C x) p ((pr2 t) x)) ((pr2 t') x))

  extensionality-universally-structured-Π :
    (t t' : universally-structured-Π C) → Id t t' ≃ htpy-universally-structured-Π t t'
  extensionality-universally-structured-Π (pair f g) =
    extensionality-Σ
      ( λ {f'} g' (H : f ~ f') → (x : A) → Id (tr (C x) (H x) (g x)) (g' x))
      ( refl-htpy)
      ( λ f' → equiv-funext)
      ( λ g' → equiv-funext)

  eq-htpy-universally-structured-Π :
    {t t' : universally-structured-Π C} → htpy-universally-structured-Π t t' → Id t t'
  eq-htpy-universally-structured-Π {t} {t'} =
    map-inv-equiv (extensionality-universally-structured-Π t t')

map-distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C → universally-structured-Π C
pr1 (map-distributive-Π-Σ φ) x = pr1 (φ x)
pr2 (map-distributive-Π-Σ φ) x = pr2 (φ x)

map-inv-distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  universally-structured-Π C → Π-total-fam C
pr1 (map-inv-distributive-Π-Σ ψ x) = (pr1 ψ) x
pr2 (map-inv-distributive-Π-Σ ψ x) = (pr2 ψ) x

issec-map-inv-distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( map-distributive-Π-Σ {A = A} {B = B} {C = C}) ∘
    ( map-inv-distributive-Π-Σ {A = A} {B = B} {C = C})) ~ id
issec-map-inv-distributive-Π-Σ {A = A} {C = C} (pair ψ ψ') =
  eq-htpy-universally-structured-Π C (pair refl-htpy refl-htpy)

isretr-map-inv-distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  ( ( map-inv-distributive-Π-Σ {A = A} {B = B} {C = C}) ∘
    ( map-distributive-Π-Σ {A = A} {B = B} {C = C})) ~ id
isretr-map-inv-distributive-Π-Σ φ =
  eq-htpy (λ x → eq-pair-Σ refl refl)

abstract
  is-equiv-map-distributive-Π-Σ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
    is-equiv (map-distributive-Π-Σ {A = A} {B = B} {C = C})
  is-equiv-map-distributive-Π-Σ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( map-inv-distributive-Π-Σ {A = A} {B = B} {C = C})
      ( issec-map-inv-distributive-Π-Σ {A = A} {B = B} {C = C})
      ( isretr-map-inv-distributive-Π-Σ {A = A} {B = B} {C = C})

distributive-Π-Σ :
  { l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  Π-total-fam C ≃ universally-structured-Π C
pr1 distributive-Π-Σ = map-distributive-Π-Σ
pr2 distributive-Π-Σ = is-equiv-map-distributive-Π-Σ

abstract
  is-equiv-map-inv-distributive-Π-Σ :
    {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
    is-equiv (map-inv-distributive-Π-Σ {A = A} {B = B} {C = C})
  is-equiv-map-inv-distributive-Π-Σ {A = A} {B = B} {C = C} =
    is-equiv-has-inverse
      ( map-distributive-Π-Σ {A = A} {B = B} {C = C})
      ( isretr-map-inv-distributive-Π-Σ {A = A} {B = B} {C = C})
      ( issec-map-inv-distributive-Π-Σ {A = A} {B = B} {C = C})

inv-distributive-Π-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3} →
  (universally-structured-Π C) ≃ (Π-total-fam C)
pr1 inv-distributive-Π-Σ = map-inv-distributive-Π-Σ
pr2 inv-distributive-Π-Σ = is-equiv-map-inv-distributive-Π-Σ
```

### Ordinary functions into a Σ-type

```agda
mapping-into-Σ :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : B → UU l3} →
  (A → Σ B C) → Σ (A → B) (λ f → (x : A) → C (f x))
mapping-into-Σ {B = B} = map-distributive-Π-Σ {B = λ x → B}

abstract
  is-equiv-mapping-into-Σ :
    {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
    {C : B → UU l3} → is-equiv (mapping-into-Σ {A = A} {C = C})
  is-equiv-mapping-into-Σ = is-equiv-map-distributive-Π-Σ
```

```agda
Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (t t' : (a : A) → Σ (B a) (C a)) → UU (l1 ⊔ (l2 ⊔ l3))
Eq-Π-total-fam {A = A} C t t' =
  Π-total-fam (λ x (p : Id (pr1 (t x)) (pr1 (t' x))) →
    Id (tr (C x) p (pr2 (t x))) (pr2 (t' x)))

extensionality-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (f g : (a : A) → Σ (B a) (C a)) → Id f g ≃ Eq-Π-total-fam C f g
extensionality-Π-total-fam C f g =
  ( inv-distributive-Π-Σ ∘e
    ( extensionality-universally-structured-Π C
      ( map-distributive-Π-Σ f)
      ( map-distributive-Π-Σ g))) ∘e
  ( equiv-ap distributive-Π-Σ f g)

eq-Eq-Π-total-fam :
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (C : (x : A) → B x → UU l3)
  (f g : (a : A) → Σ (B a) (C a)) → Eq-Π-total-fam C f g → Id f g
eq-Eq-Π-total-fam C f g = map-inv-equiv (extensionality-Π-total-fam C f g)
```
