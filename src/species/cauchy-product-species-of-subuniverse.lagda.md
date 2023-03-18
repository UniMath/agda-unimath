# Cauchy products of species of subuniverse

```agda
module species.cauchy-product-species-of-subuniverse where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels

open import species.species-of-types-in-subuniverse
```

</details>

## Idea

The Cauchy product of two species of subuniverse `S` and `T` from `P` to `Q` on
`X` is defined as

```md
  Σ (k : P) (Σ (k' : P) (Σ (e : k + k' ≃ X) S(k) × T(k')))
```

If `Q` is stable by product and dependent pair type over `P` type, then the
cauchy product is also a species of subuniverse from `P` to `Q`

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  where

  private
    Ql2 = subuniverse-global-subuniverse Q l2
    Ql3 = subuniverse-global-subuniverse Q l3
    Ql1+⊔l2⊔l3 = subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3)

  cauchy-prod-species-subuniverse' :
    (S : species-subuniverse P Ql2) (T : species-subuniverse P Ql3)
    (X : type-subuniverse P) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  cauchy-prod-species-subuniverse' S T X =
    Σ ( binary-coproduct-Decomposition P X)
      ( λ d →
        inclusion-subuniverse Ql2
          ( S (pr1-binary-coproduct-Decomposition P X d)) ×
        inclusion-subuniverse Ql3
          ( T (pr2-binary-coproduct-Decomposition P X d)))

module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id )
  ( C1 :
    ( (l4 l5 : Level)
    (S : species-subuniverse P (subuniverse-global-subuniverse Q l4))
    (T : species-subuniverse P (subuniverse-global-subuniverse Q l5))
    (X : type-subuniverse P) →
      is-in-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l4 ⊔ l5))
        ( cauchy-prod-species-subuniverse' P Q S T X)))
  where

  private
    Ql2 = subuniverse-global-subuniverse Q l2
    Ql3 = subuniverse-global-subuniverse Q l3
    Ql1+⊔l2⊔l3 = subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3)

  cauchy-prod-species-subuniverse :
    species-subuniverse P Ql2 → species-subuniverse P Ql3 →
    species-subuniverse P Ql1+⊔l2⊔l3
  pr1 (cauchy-prod-species-subuniverse S T X) =
    cauchy-prod-species-subuniverse' P Q S T X
  pr2 (cauchy-prod-species-subuniverse S T X) = C1 l2 l3 S T X

module _
  {l1 l2 l3 l4 : Level} (P : subuniverse l1 l1) (Q : global-subuniverse id)
  ( C1 :
      ( (l5 l6 : Level)
        (S : species-subuniverse P (subuniverse-global-subuniverse Q l5))
        (T : species-subuniverse P (subuniverse-global-subuniverse Q l6))
        (X : type-subuniverse P) →
        is-in-subuniverse
          ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l5 ⊔ l6) )
          ( cauchy-prod-species-subuniverse' P Q S T X)))
  ( C2 :
    (A B : type-subuniverse P) →
    is-in-subuniverse P (inclusion-subuniverse P A + inclusion-subuniverse P B))
  where

  private
    Ql2 = subuniverse-global-subuniverse Q l2
    Ql3 = subuniverse-global-subuniverse Q l3
    Ql4 = subuniverse-global-subuniverse Q l4

  module _
    (S : species-subuniverse P Ql2)
    (T : species-subuniverse P Ql3)
    (U : species-subuniverse P Ql4)
    (X : type-subuniverse P)
    where

    equiv-left-iterated-cauchy-prod-species-subuniverse :
      cauchy-prod-species-subuniverse' P Q
        ( cauchy-prod-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      Σ ( ternary-coproduct-Decomposition P X)
        ( λ d →
          inclusion-subuniverse Ql2
            ( S (fst-ternary-coproduct-Decomposition P X d)) ×
            ( inclusion-subuniverse Ql3
              ( T (snd-ternary-coproduct-Decomposition P X d)) ×
              inclusion-subuniverse Ql4
              ( U (thrd-ternary-coproduct-Decomposition P X d))))
    equiv-left-iterated-cauchy-prod-species-subuniverse =
      ( ( equiv-Σ
          ( λ d →
            inclusion-subuniverse Ql2
            ( S (fst-ternary-coproduct-Decomposition P X d)) ×
            ( inclusion-subuniverse Ql3
              ( T (snd-ternary-coproduct-Decomposition P X d)) ×
              inclusion-subuniverse Ql4
              ( U (thrd-ternary-coproduct-Decomposition P X d)))))
          ( ( equiv-Σ
              ( _)
              ( assoc-prod _ _ _ ∘e commutative-prod)
              ( λ x →
                equiv-postcomp-equiv
                  ( ( ( assoc-coprod) ∘e
                    ( ( commutative-coprod  _ _))) )
                  ( inclusion-subuniverse P X)) ∘e
              equiv-ternary-left-iterated-coproduct-Decomposition P X C2))
          ( λ d → assoc-prod _ _ _) ∘e
      ( ( inv-assoc-Σ
          ( binary-coproduct-Decomposition P X)
          ( λ z → binary-coproduct-Decomposition P (pr1 z))
          ( _)) ∘e
      ( ( equiv-tot  λ d → right-distributive-prod-Σ))))

    equiv-right-iterated-cauchy-prod-species-subuniverse :
      cauchy-prod-species-subuniverse' P Q
        ( S)
        ( cauchy-prod-species-subuniverse P Q C1 T U)
        ( X) ≃
      Σ ( ternary-coproduct-Decomposition P X)
        ( λ d →
          inclusion-subuniverse Ql2
            ( S (fst-ternary-coproduct-Decomposition P X d)) ×
            ( inclusion-subuniverse Ql3
              ( T (snd-ternary-coproduct-Decomposition P X d)) ×
                inclusion-subuniverse Ql4
              ( U (thrd-ternary-coproduct-Decomposition P X d))))
    equiv-right-iterated-cauchy-prod-species-subuniverse =
      ( ( equiv-Σ-equiv-base
          ( _)
          ( equiv-ternary-right-iterated-coproduct-Decomposition P X C2)) ∘e
      ( ( inv-assoc-Σ
          ( binary-coproduct-Decomposition P X)
          ( λ z → binary-coproduct-Decomposition P (pr1 (pr2 z)))
          ( _)) ∘e
      ( ( equiv-tot (λ d → left-distributive-prod-Σ)))))

    equiv-assoc-cauchy-prod-species-subuniverse :
      cauchy-prod-species-subuniverse' P Q
        ( cauchy-prod-species-subuniverse P Q C1 S T)
        ( U)
        ( X) ≃
      cauchy-prod-species-subuniverse' P Q
        ( S)
        ( cauchy-prod-species-subuniverse P Q C1 T U)
        ( X)
    equiv-assoc-cauchy-prod-species-subuniverse =
      inv-equiv (equiv-right-iterated-cauchy-prod-species-subuniverse) ∘e
      equiv-left-iterated-cauchy-prod-species-subuniverse

  module _
    (S : species-subuniverse P Ql2)
    (T : species-subuniverse P Ql3)
    (U : species-subuniverse P Ql4)
    where

    assoc-cauchy-prod-species-subuniverse :
      cauchy-prod-species-subuniverse P Q C1
        ( cauchy-prod-species-subuniverse P Q C1 S T)
        ( U) ＝
      cauchy-prod-species-subuniverse P Q C1
        ( S)
        ( cauchy-prod-species-subuniverse P Q C1 T U)
    assoc-cauchy-prod-species-subuniverse =
      eq-equiv-fam-subuniverse
        ( subuniverse-global-subuniverse Q (lsuc l1 ⊔ l2 ⊔ l3 ⊔ l4))
        ( cauchy-prod-species-subuniverse P Q C1
          ( cauchy-prod-species-subuniverse P Q C1 S T)
          ( U))
        ( cauchy-prod-species-subuniverse P Q C1
          ( S)
          ( cauchy-prod-species-subuniverse P Q C1 T U))
        ( equiv-assoc-cauchy-prod-species-subuniverse S T U)
```
