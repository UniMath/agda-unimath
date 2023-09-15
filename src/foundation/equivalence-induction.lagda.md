# Equivalence induction

```agda
module foundation.equivalence-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-systems
open import foundation.subuniverses
open import foundation.univalence
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.sections
open import foundation-core.singleton-induction
```

</details>

## Idea

**Equivalence induction** is the principle asserting that for any type family

```text
  P : (B : 𝒰) (e : A ≃ B) → 𝒰
```

of types indexed by all [equivalences](foundation.equivalences.md) with domain
`A`, there is a [section](foundation.sections.md) of the evaluation map

```text
  ((B : 𝒰) (e : A ≃ B) → P B e) → P A id-equiv.
```

The principle of equivalence induction is equivalent to the
[univalence axiom](foundation.univalence.md).

By equivalence induction, it follows that any type family `P : 𝒰 → 𝒱` on the
universe has an
[action on equivalences](foundation.action-on-equivalences-type-families.md)

```text
  (A ≃ B) → P A ≃ P B.
```

## Statement

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  ev-id-equiv :
    {l : Level} (P : (B : UU l1) → (A ≃ B) → UU l) →
    ((B : UU l1) (e : A ≃ B) → P B e) → P A id-equiv
  ev-id-equiv P f = f A id-equiv

  induction-principle-equivalences :
    {l : Level} (P : (B : UU l1) (e : A ≃ B) → UU l) → UU (lsuc l1 ⊔ l)
  induction-principle-equivalences P = section (ev-id-equiv P)

  triangle-ev-id-equiv :
    {l : Level}
    (P : (Σ (UU l1) (λ X → A ≃ X)) → UU l) →
    coherence-triangle-maps
      ( ev-point (A , id-equiv) {P})
      ( ev-id-equiv (λ X e → P (X , e)))
      ( ev-pair {A = UU l1} {B = λ X → A ≃ X} {C = P})
  triangle-ev-id-equiv P f = refl
```

## Properties

### Equivalence induction is equivalent to the contractibility of the total space of equivalences

#### Contractibility of the total space of equivalences implies equivalence induction

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-identity-system-is-contr-total-equiv :
      is-contr (Σ (UU l1) (λ X → A ≃ X)) →
      {l : Level} →
      (P : (Σ (UU l1) (λ X → A ≃ X)) → UU l) →
      induction-principle-equivalences (λ B e → P (B , e))
    is-identity-system-is-contr-total-equiv c P =
      section-left-factor
        ( ev-id-equiv (λ X e → P (X , e)))
        ( ev-pair)
        ( is-singleton-is-contr
          ( A , id-equiv)
          ( ( A , id-equiv) ,
            ( λ t →
              ( inv (contraction c (A , id-equiv))) ∙ (contraction c t)))
          ( P))
```

#### Equivalence induction implies contractibility of the total space of equivalences

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  abstract
    is-contr-total-is-identity-system-equiv :
      ( {l : Level} → is-identity-system l (λ X → A ≃ X) A id-equiv) →
      is-contr (Σ (UU l1) (λ X → A ≃ X))
    is-contr-total-is-identity-system-equiv ind =
      is-contr-is-singleton
        ( Σ (UU l1) (λ X → A ≃ X))
        ( A , id-equiv)
        ( λ P → section-comp
          ( ev-id-equiv (λ X e → P (X , e)))
          ( ev-pair {A = UU l1} {B = λ X → A ≃ X} {C = P})
          ( ind-Σ , refl-htpy)
          ( ind (λ X e → P (X , e))))
```

### Equivalence induction in a universe

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : (B : UU l1) (e : A ≃ B) → UU l2)
  where

  abstract
    is-identity-system-equiv : section (ev-id-equiv P)
    is-identity-system-equiv =
      is-identity-system-is-contr-total-equiv
        ( is-contr-total-equiv _)
        ( λ t → P (pr1 t) (pr2 t))

  ind-equiv :
    P A id-equiv → {B : UU l1} (e : A ≃ B) → P B e
  ind-equiv p {B} = pr1 is-identity-system-equiv p B

  compute-ind-equiv :
    (u : P A id-equiv) → ind-equiv u id-equiv ＝ u
  compute-ind-equiv = pr2 is-identity-system-equiv
```

### Equivalence induction in a subuniverse

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (A : type-subuniverse P)
  where

  ev-id-equiv-subuniverse :
    {F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3} →
    ((B : type-subuniverse P) (e : equiv-subuniverse P A B) → F B e) →
    F A id-equiv
  ev-id-equiv-subuniverse f = f A id-equiv

  triangle-ev-id-equiv-subuniverse :
    (F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3) →
    coherence-triangle-maps
      ( ev-point (A , id-equiv))
      ( ev-id-equiv-subuniverse {F})
      ( ev-pair)
  triangle-ev-id-equiv-subuniverse F E = refl

  abstract
    is-identity-system-equiv-subuniverse :
      (F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3) →
      section (ev-id-equiv-subuniverse {F})
    is-identity-system-equiv-subuniverse =
      is-identity-system-is-torsorial A id-equiv
        ( is-contr-total-equiv-subuniverse P A)

  ind-equiv-subuniverse :
    (F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3) →
    F A id-equiv → (B : type-subuniverse P) (e : equiv-subuniverse P A B) →
    F B e
  ind-equiv-subuniverse F =
    pr1 (is-identity-system-equiv-subuniverse F)

  compute-ind-equiv-subuniverse :
    (F : (B : type-subuniverse P) → equiv-subuniverse P A B → UU l3) →
    (u : F A id-equiv) →
    ind-equiv-subuniverse F u A id-equiv ＝ u
  compute-ind-equiv-subuniverse F =
    pr2 (is-identity-system-equiv-subuniverse F)
```

### The evaluation map `ev-id-equiv` is an equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : (B : UU l1) (e : A ≃ B) → UU l2)
  where

  is-equiv-ev-id-equiv : is-equiv (ev-id-equiv P)
  is-equiv-ev-id-equiv =
    is-equiv-left-factor-htpy
      ( ev-point (A , id-equiv))
      ( ev-id-equiv P)
      ( ev-pair)
      ( triangle-ev-id-equiv (λ u → P (pr1 u) (pr2 u)))
      ( dependent-universal-property-contr-is-contr
        ( A , id-equiv)
        ( is-contr-total-equiv A)
        ( λ u → P (pr1 u) (pr2 u)))
      ( is-equiv-ev-pair)

  is-contr-map-ev-id-equiv : is-contr-map (ev-id-equiv P)
  is-contr-map-ev-id-equiv = is-contr-map-is-equiv is-equiv-ev-id-equiv
```

### The evaluation map `ev-id-equiv-subuniverse` is an equivalence

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (F : (Y : type-subuniverse P) (e : equiv-subuniverse P X Y) → UU l3)
  where

  is-equiv-ev-id-equiv-subuniverse :
    is-equiv (ev-id-equiv-subuniverse P X {F})
  is-equiv-ev-id-equiv-subuniverse =
    is-equiv-left-factor-htpy
      ( ev-point (X , id-equiv))
      ( ev-id-equiv-subuniverse P X)
      ( ev-pair)
      ( triangle-ev-id-equiv-subuniverse P X F)
      ( dependent-universal-property-contr-is-contr
        ( X , id-equiv)
        ( is-contr-total-equiv-subuniverse P X)
        ( λ E → F (pr1 E) (pr2 E)))
      ( is-equiv-ev-pair)

  is-contr-map-ev-id-equiv-subuniverse :
    is-contr-map (ev-id-equiv-subuniverse P X {F})
  is-contr-map-ev-id-equiv-subuniverse =
    is-contr-map-is-equiv is-equiv-ev-id-equiv-subuniverse
```

### Equivalence induction implies that postcomposing by an equivalence is an equivalence

Of course we already know that this fact follows from
[function extensionality](foundation.function-extensionality.md). However, we
prove it again from equivalence induction so that we can prove that
[univalence implies function extensionality](foundation.univalence-implies-function-extensionality.md).

```agda
abstract
  is-equiv-postcomp-univalence :
    {l1 l2 : Level} {X Y : UU l1} (A : UU l2) (e : X ≃ Y) →
    is-equiv (postcomp A (map-equiv e))
  is-equiv-postcomp-univalence {X = X} A =
    ind-equiv (λ Y e → is-equiv (postcomp A (map-equiv e))) is-equiv-id
```
