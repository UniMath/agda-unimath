# Equivalence extensionality

```agda
module foundation.equivalence-extensionality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-systems
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sections
open import foundation-core.torsorial-type-families
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Characterizing the identity type of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  htpy-equiv : A ≃ B → A ≃ B → UU (l1 ⊔ l2)
  htpy-equiv e e' = (map-equiv e) ~ (map-equiv e')

  _~e_ = htpy-equiv

  extensionality-equiv : (f g : A ≃ B) → (f ＝ g) ≃ htpy-equiv f g
  extensionality-equiv f =
    extensionality-type-subtype
      ( is-equiv-Prop)
      ( pr2 f)
      ( refl-htpy' (pr1 f))
      ( λ g → equiv-funext)
    where
    is-equiv-Prop : (f : A → B) → Prop (l1 ⊔ l2)
    pr1 (is-equiv-Prop f) = is-equiv f
    pr2 (is-equiv-Prop f) H =
      is-prop-is-contr
        ( is-contr-prod
          ( is-contr-equiv'
            ( (b : B) → fiber f b)
            ( distributive-Π-Σ)
            ( is-contr-Π (is-contr-map-is-equiv H)))
          ( is-contr-is-equiv'
            ( Σ (B → A) (λ h → (h ∘ f) ＝ id))
            ( tot (λ h → htpy-eq))
            ( is-equiv-tot-is-fiberwise-equiv
              ( λ h → funext (h ∘ f) id))
            ( is-contr-map-is-equiv
              ( is-equiv-precomp-Π-is-equiv H (λ y → A))
              ( id))))
        ( H)

  abstract
    is-torsorial-htpy-equiv :
      (e : A ≃ B) → is-torsorial (htpy-equiv e)
    is-torsorial-htpy-equiv e =
      fundamental-theorem-id'
        ( map-equiv ∘ extensionality-equiv e)
        ( is-equiv-map-equiv ∘ extensionality-equiv e)

  refl-htpy-equiv : (e : A ≃ B) → htpy-equiv e e
  refl-htpy-equiv e = refl-htpy

  eq-htpy-equiv : {e e' : A ≃ B} → htpy-equiv e e' → e ＝ e'
  eq-htpy-equiv {e} {e'} = map-inv-equiv (extensionality-equiv e e')

  htpy-eq-equiv : {e e' : A ≃ B} → e ＝ e' → htpy-equiv e e'
  htpy-eq-equiv {e} {e'} = map-equiv (extensionality-equiv e e')

  htpy-eq-map-equiv :
    {e e' : A ≃ B} → (map-equiv e) ＝ (map-equiv e') → htpy-equiv e e'
  htpy-eq-map-equiv = htpy-eq
```

### Homotopy induction for homotopies between equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    induction-principle-htpy-equiv :
      {l3 : Level} (e : A ≃ B)
      (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
      section
        ( λ (h : (e' : A ≃ B) (H : htpy-equiv e e') → P e' H) →
          h e (refl-htpy-equiv e))
    induction-principle-htpy-equiv e =
      is-identity-system-is-torsorial e
        ( refl-htpy-equiv e)
        ( is-torsorial-htpy-equiv e)

  ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3) →
    P e (refl-htpy-equiv e) → (e' : A ≃ B) (H : htpy-equiv e e') → P e' H
  ind-htpy-equiv e P = pr1 (induction-principle-htpy-equiv e P)

  compute-ind-htpy-equiv :
    {l3 : Level} (e : A ≃ B) (P : (e' : A ≃ B) (H : htpy-equiv e e') → UU l3)
    (p : P e (refl-htpy-equiv e)) →
    ind-htpy-equiv e P p e (refl-htpy-equiv e) ＝ p
  compute-ind-htpy-equiv e P = pr2 (induction-principle-htpy-equiv e P)
```
