# Coproduct decompositions

```agda
module univalent-combinatorics.coproduct-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.subuniverses
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels
```

</details>

## Definitions

### Binary coproduct decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  binary-coproduct-Decomposition : UU (lsuc l1 ⊔ l2)
  binary-coproduct-Decomposition =
    Σ ( type-subuniverse P)
        ( λ k1 →
          Σ ( type-subuniverse P)
            ( λ k2 →
              ( inclusion-subuniverse P X ≃
                ( (inclusion-subuniverse P k1) +
                  (inclusion-subuniverse P k2)))))

module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (d : binary-coproduct-Decomposition P X)
  where

  pr1-binary-coproduct-Decomposition : type-subuniverse P
  pr1-binary-coproduct-Decomposition = pr1 d

  inclusion-pr1-binary-coproduct-Decomposition : UU l1
  inclusion-pr1-binary-coproduct-Decomposition =
    inclusion-subuniverse P pr1-binary-coproduct-Decomposition

  pr2-binary-coproduct-Decomposition : type-subuniverse P
  pr2-binary-coproduct-Decomposition = pr1 (pr2 d)

  inclusion-pr2-binary-coproduct-Decomposition : UU l1
  inclusion-pr2-binary-coproduct-Decomposition =
    inclusion-subuniverse P pr2-binary-coproduct-Decomposition

  matching-correspondence-coproductuct-decomposition :
    inclusion-subuniverse P X ≃
    ( inclusion-pr1-binary-coproduct-Decomposition +
      inclusion-pr2-binary-coproduct-Decomposition)
  matching-correspondence-coproductuct-decomposition = pr2 (pr2 d)
```

### Iterated binary coproduct decompositions

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  left-iterated-binary-coproduct-Decomposition : UU (lsuc l1 ⊔ l2)
  left-iterated-binary-coproduct-Decomposition =
    Σ ( binary-coproduct-Decomposition P X)
      ( λ d →
        binary-coproduct-Decomposition
          ( P)
          ( pr1-binary-coproduct-Decomposition P X d))

  right-iterated-binary-coproduct-Decomposition : UU (lsuc l1 ⊔ l2)
  right-iterated-binary-coproduct-Decomposition =
    Σ ( binary-coproduct-Decomposition P X)
       ( λ d →
         binary-coproduct-Decomposition
           ( P)
           ( pr2-binary-coproduct-Decomposition P X d))
```

### Ternary coproduct Decompositions

```agda
module _
  {l1 l2} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  ternary-coproduct-Decomposition : UU (lsuc l1 ⊔ l2)
  ternary-coproduct-Decomposition =
    Σ ( type-subuniverse P × (type-subuniverse P × type-subuniverse P))
       ( λ x →
         inclusion-subuniverse P X ≃
         ( inclusion-subuniverse P (pr1 x) +
           ( inclusion-subuniverse P (pr1 (pr2 x)) +
             inclusion-subuniverse P (pr2 (pr2 x)))) )

```

## Propositions

### Equivalence between binary corpoduct Decomposition induce by commutativiy of coproduct

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  where

  equiv-commutative-binary-coproduct-Decomposition :
    binary-coproduct-Decomposition P X ≃ binary-coproduct-Decomposition P X
  equiv-commutative-binary-coproduct-Decomposition =
    ( ( assoc-Σ
        ( type-subuniverse P)
        ( λ _ → type-subuniverse P)
        ( _)) ∘e
    ( ( equiv-Σ
        ( _)
        ( commutative-prod)
        ( λ x →
          equiv-postcomp-equiv
            ( commutative-coprod
              ( inclusion-subuniverse P (pr1 x))
              ( inclusion-subuniverse P (pr2 x)))
            (inclusion-subuniverse P X))) ∘e
    ( ( inv-assoc-Σ
        ( type-subuniverse P)
        ( λ _ → type-subuniverse P)
        ( _)))))
```

### Equivalence between iterated coproduct and ternary coproduct decomposition

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : type-subuniverse P)
  (C1 :
    (A : type-subuniverse P) → (B : type-subuniverse P) →
    is-in-subuniverse P (inclusion-subuniverse P A + inclusion-subuniverse P B))
  where

```
