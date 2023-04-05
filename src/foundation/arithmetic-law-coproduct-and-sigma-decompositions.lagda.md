# Arithmetic law for coproduct decomposition and Σ-decomposition

```agda
module foundation.arithmetic-law-coproduct-and-sigma-decompositions where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.coproduct-decompositions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.relaxed-sigma-decompositions
open import foundation.type-arithmetic-coproduct-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universal-property-coproduct-types
open import foundation.universe-levels
```

</details>

## Propositions

### Coproduct decomposition of the indexing type of a relaxed Σ-decomposition are equivalent to relaxed Σ-decomposition of the left and right summand of a coproduct decomposition.

```agda
module _
  {l : Level} {X : UU l}
  where

  private
    reassociate :
      Σ (Relaxed-Σ-Decomposition l l X)
        ( λ d → binary-coproduct-Decomposition l l
          ( indexing-type-Relaxed-Σ-Decomposition d)) ≃
        Σ ( UU l)
          ( λ A →
             Σ ( UU l)
               ( λ B →
                 Σ ( Σ ( UU l) λ U → ( U ≃ (A + B)))
                   ( λ U → Σ (pr1 U → UU l) (λ Y → X ≃ Σ (pr1 U) Y ))))
    pr1 reassociate ((U , V , f) , A , B , e) = (A , B , (U , e) , V , f)
    pr2 reassociate =
      is-equiv-has-inverse
        ( λ (A , B , (U , e) , V , f) → ((U , V , f) , A , B , e))
        ( refl-htpy)
        ( refl-htpy)

    reassociate' :
      Σ ( UU l)
        ( λ A →
          Σ ( UU l)
            ( λ B →
              Σ ( (A → UU l) × (B → UU l))
                ( λ (YA , YB) →
                  Σ ( Σ (UU l) (λ A' → A' ≃ Σ A YA))
                    ( λ A' →
                      Σ ( Σ (UU l) (λ B' → B' ≃ Σ B YB))
                        ( λ B' → X ≃ (pr1 A' + pr1 B')))))) ≃
      Σ ( binary-coproduct-Decomposition l l X)
      ( λ d →
        Relaxed-Σ-Decomposition l l
          ( left-summand-binary-coproduct-Decomposition d) ×
        Relaxed-Σ-Decomposition l l
          ( right-summand-binary-coproduct-Decomposition d) )
    pr1 reassociate' (A , B , (YA , YB) , (A' , eA) , (B' , eB) , e) =
      (A' , B' , e) , ((A , YA , eA) , B , YB , eB)
    pr2 reassociate' =
      is-equiv-has-inverse
        ( λ ((A' , B' , e) , ((A , YA , eA) , B , YB , eB)) →
          (A , B , (YA , YB) , (A' , eA) , (B' , eB) , e))
        ( refl-htpy)
        ( refl-htpy)

  equiv-binary-coproduct-Decomposition-Σ-Decomposition :
    Σ ( Relaxed-Σ-Decomposition l l X)
      ( λ d →
        binary-coproduct-Decomposition l l
         ( indexing-type-Relaxed-Σ-Decomposition d)) ≃
    Σ ( binary-coproduct-Decomposition l l X)
      ( λ d →
        Relaxed-Σ-Decomposition l l
          ( left-summand-binary-coproduct-Decomposition d) ×
        Relaxed-Σ-Decomposition l l
          ( right-summand-binary-coproduct-Decomposition d) )

  equiv-binary-coproduct-Decomposition-Σ-Decomposition =
    ( ( reassociate') ∘e
      ( ( equiv-tot
            ( λ A →
              equiv-tot
                ( λ B →
                  ( ( equiv-tot
                        ( λ ( YA , YB) →
                          ( ( equiv-tot
                              ( λ A' →
                                equiv-tot
                                  ( λ B' →
                                    equiv-postcomp-equiv
                                      ( equiv-coprod
                                        ( inv-equiv (pr2 A'))
                                        ( inv-equiv (pr2 B')))
                                      ( X))) ∘e
                            ( ( inv-left-unit-law-Σ-is-contr
                                  ( is-contr-total-equiv' (Σ A YA))
                                  ( Σ A YA , id-equiv)) ∘e
                              ( inv-left-unit-law-Σ-is-contr
                                  ( is-contr-total-equiv' (Σ B YB))
                                  ( Σ B YB , id-equiv)))))) ∘e
                    ( ( equiv-Σ-equiv-base
                          ( λ (YA , YB) → X ≃ (Σ A YA + Σ B YB))
                          ( equiv-universal-property-coprod (UU l))) ∘e
                      ( ( equiv-tot
                            ( λ Y →
                              equiv-postcomp-equiv
                                ( right-distributive-Σ-coprod A B Y)
                                ( X))) ∘e
                          ( left-unit-law-Σ-is-contr
                              ( is-contr-total-equiv' (A + B))
                              ((A + B) , id-equiv))))))))) ∘e
      ( reassociate)))
```
