# Axiom L

```agda
module foundation.axiom-l where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddings
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.sets
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-identity-types

open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.functions
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.univalence
open import foundation-core.universe-levels
```

</details>

## Idea

Axiom L, which is due to Peter Lumsdaine, asserts that for any two types `X` and `Y` in a common universe, the map `X ＝ Y → X ≃ Y` is an embedding. This axiom is a common generalization of the univalence axiom and axiom K, in the sense that both univalence and axiom K imply axiom L.

## Definition

```agda
axiom-L : (l : Level) → UU (lsuc l)
axiom-L l = (X Y : UU l) → is-emb (equiv-eq {A = X} {B = Y})

emb-L : {l : Level} → axiom-L l → (X Y : UU l) → (X ＝ Y) ↪ (X ≃ Y)
pr1 (emb-L H X Y) = equiv-eq
pr2 (emb-L H X Y) = H X Y
```

## Properties

### Axiom L generalizes the univalence axiom

```agda
axiom-L-univalence :
  {l : Level} → ((A B : UU l) → UNIVALENCE A B) → axiom-L l
axiom-L-univalence ua A B = is-emb-is-equiv (ua A B)
```

### Axiom L generalizes axiom K

```agda
axiom-L-axiom-K :
  {l : Level} → ((A : UU l) → axiom-K A) → axiom-K (UU l) → axiom-L l
axiom-L-axiom-K K K-UU A B =
  is-emb-is-prop-is-set
    ( is-set-axiom-K K-UU A B)
    ( is-set-equiv-is-set
      ( is-set-axiom-K (K A))
      ( is-set-axiom-K (K B)))
```

### Axiom L implies that `Id : A → A → UU l` is an embedding

```agda
module _
  {l : Level} (L : axiom-L l) (A : UU l)
  where

  is-emb-Id : is-emb (Id {A = A})
  is-emb-Id x =
    fundamental-theorem-id
      ( pair
        ( pair x refl)
        ( λ _ →
          is-injective-emb
            ( emb-fib x)
            ( eq-is-contr (is-contr-total-path x))))
      ( λ _ → ap Id)
    where
    emb-fib : (x : A) → fib' Id (Id x) ↪ Σ A (Id x)
    emb-fib x =
      comp-emb
        ( comp-emb
          ( emb-equiv
            ( equiv-tot
              ( λ y →
                ( equiv-ev-refl y) ∘e
                ( ( equiv-inclusion-is-full-subtype
                    ( Π-Prop A ∘ (is-equiv-Prop ∘_))
                    ( fundamental-theorem-id (is-contr-total-path x))) ∘e
                  ( distributive-Π-Σ)))))
          ( emb-Σ
            ( λ y → (z : A) → Id y z ≃ Id x z)
            ( id-emb)
            ( λ y →
              comp-emb
                ( emb-Π (λ z → emb-L L (Id y z) (Id x z)))
                ( emb-equiv equiv-funext))))
        ( emb-equiv (inv-equiv (equiv-fib Id (Id x))))
```
