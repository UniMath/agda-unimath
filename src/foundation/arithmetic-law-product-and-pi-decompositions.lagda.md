# Arithmetic law for product decomposition and Π-decomposition

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.arithmetic-law-product-and-pi-decompositions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-decompositions funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.functoriality-cartesian-product-types funext
open import foundation.pi-decompositions funext univalence
open import foundation.product-decompositions
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence funext univalence
open import foundation.universal-property-coproduct-types funext
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.contractible-types
open import foundation-core.coproduct-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications
```

</details>

## Idea

Let `X` be a type, we have the following equivalence :

```text
  Σ ( (U , V , e) : Π-Decomposition X)
    ( binary-product-Decomposition U) ≃
  Σ ( (A , B , e) : binary-product-Decomposition X)
    ( Π-Decomposition A ×
      Π-Decomposition B )
```

We also show a computational rule to simplify the use of this equivalence.

## Propositions

### Product decompositions of the indexing type of a Π-decomposition are equivalent to Π-decomposition of the left and right summand of a product decomposition

```agda
module _
  {l : Level} {X : UU l}
  where

  private
    reassociate :
      Σ (Π-Decomposition l l X)
        ( λ d → binary-coproduct-Decomposition l l
          ( indexing-type-Π-Decomposition d)) ≃
        Σ ( UU l)
          ( λ A →
            Σ ( UU l)
              ( λ B →
                Σ ( Σ ( UU l) λ U → ( U ≃ (A + B)))
                  ( λ U → Σ (pr1 U → UU l) (λ Y → X ≃ Π (pr1 U) Y))))
    pr1 reassociate ((U , V , f) , A , B , e) = (A , B , (U , e) , V , f)
    pr2 reassociate =
      is-equiv-is-invertible
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
                  Σ ( Σ (UU l) (λ A' → A' ≃ Π A YA))
                    ( λ A' →
                      Σ ( Σ (UU l) (λ B' → B' ≃ Π B YB))
                        ( λ B' → X ≃ (pr1 A' × pr1 B')))))) ≃
      Σ ( binary-product-Decomposition l l X)
      ( λ d →
        Π-Decomposition l l
          ( left-summand-binary-product-Decomposition d) ×
        Π-Decomposition l l
          ( right-summand-binary-product-Decomposition d))
    pr1 reassociate' (A , B , (YA , YB) , (A' , eA) , (B' , eB) , e) =
      (A' , B' , e) , ((A , YA , eA) , B , YB , eB)
    pr2 reassociate' =
      is-equiv-is-invertible
        ( λ ((A' , B' , e) , ((A , YA , eA) , B , YB , eB)) →
          (A , B , (YA , YB) , (A' , eA) , (B' , eB) , e))
        ( refl-htpy)
        ( refl-htpy)

  equiv-binary-product-Decomposition-Π-Decomposition :
    Σ ( Π-Decomposition l l X)
      ( λ d →
        binary-coproduct-Decomposition l l (indexing-type-Π-Decomposition d)) ≃
    Σ ( binary-product-Decomposition l l X)
      ( λ d →
        Π-Decomposition l l
          ( left-summand-binary-product-Decomposition d) ×
        Π-Decomposition l l
          ( right-summand-binary-product-Decomposition d))

  equiv-binary-product-Decomposition-Π-Decomposition =
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
                                      ( equiv-product
                                        ( inv-equiv (pr2 A'))
                                        ( inv-equiv (pr2 B')))
                                      ( X))) ∘e
                            ( ( inv-left-unit-law-Σ-is-contr
                                  ( is-torsorial-equiv' (Π A YA))
                                  ( Π A YA , id-equiv)) ∘e
                              ( inv-left-unit-law-Σ-is-contr
                                  ( is-torsorial-equiv' (Π B YB))
                                  ( Π B YB , id-equiv)))))) ∘e
                    ( ( equiv-Σ-equiv-base
                        ( λ z → X ≃ (Π A (pr1 z) × Π B (pr2 z)))
                        ( equiv-universal-property-coproduct (UU l))) ∘e
                      ( ( equiv-tot
                            ( λ Y →
                              equiv-postcomp-equiv
                                ( equiv-dependent-universal-property-coproduct
                                  ( Y))
                                ( X))) ∘e
                          ( left-unit-law-Σ-is-contr
                              ( is-torsorial-equiv' (A + B))
                              ((A + B) , id-equiv))))))))) ∘e
      ( reassociate)))

  module _
    ( D : Σ ( Π-Decomposition l l X)
            ( λ D →
              binary-coproduct-Decomposition
                l l
                ( indexing-type-Π-Decomposition D)))
    where

    private
      tr-total-equiv :
        {l1 l3 l4 : Level} {X Y : UU l1} (e : Y ≃ X) →
        (h : Id {A = Σ (UU l1) λ Y → Y ≃ X} (X , id-equiv) (Y , e)) →
        {C : (X : UU l1) → (X → UU l3) → UU l4} →
        {f : Σ (Y → UU l3) (λ Z → C Y Z)} →
        (x : X) →
        pr1
          ( tr
            ( λ Y →
              ( Σ ( pr1 Y → UU l3)
                  ( λ Z → C (pr1 Y) Z) →
                Σ ( X → UU l3)
                  ( λ Z → C X Z)))
            ( h)
            ( id)
            ( f))
          ( x) ＝
        pr1 f (map-inv-equiv e x)
      tr-total-equiv e refl x = refl

    compute-left-equiv-binary-product-Decomposition-Π-Decomposition :
      ( a : left-summand-binary-coproduct-Decomposition (pr2 D)) →
      cotype-Π-Decomposition
        ( pr1
          ( pr2
            ( map-equiv equiv-binary-product-Decomposition-Π-Decomposition
              ( D))))
        ( a) ＝
      cotype-Π-Decomposition
        ( pr1 D)
        ( map-inv-equiv
          ( matching-correspondence-binary-coproduct-Decomposition (pr2 D))
          ( inl a))
    compute-left-equiv-binary-product-Decomposition-Π-Decomposition a =
      tr-total-equiv
        ( matching-correspondence-binary-coproduct-Decomposition (pr2 D))
        ( inv
            ( contraction
                ( is-torsorial-equiv' (pr1 (pr2 D) + pr1 (pr2 (pr2 D))))
                ( (pr1 (pr2 D) + pr1 (pr2 (pr2 D))) , id-equiv)) ∙
          contraction
            ( is-torsorial-equiv' (pr1 (pr2 D) + pr1 (pr2 (pr2 D))))
                ( pr1 (pr1 D) , pr2 (pr2 (pr2 D))))
        ( inl a)

    compute-right-equiv-binary-product-Decomposition-Π-Decomposition :
      ( b : right-summand-binary-coproduct-Decomposition (pr2 D)) →
      cotype-Π-Decomposition
        ( pr2
          ( pr2
            ( map-equiv equiv-binary-product-Decomposition-Π-Decomposition
              ( D))))
        ( b) ＝
      cotype-Π-Decomposition (pr1 D)
        ( map-inv-equiv
          ( matching-correspondence-binary-coproduct-Decomposition (pr2 D))
          ( inr b))
    compute-right-equiv-binary-product-Decomposition-Π-Decomposition b =
      tr-total-equiv
          ( matching-correspondence-binary-coproduct-Decomposition (pr2 D))
          ( inv
              ( contraction
                  ( is-torsorial-equiv' (pr1 (pr2 D) + pr1 (pr2 (pr2 D))))
                  ( (pr1 (pr2 D) + pr1 (pr2 (pr2 D))) , id-equiv)) ∙
            contraction
              ( is-torsorial-equiv' (pr1 (pr2 D) + pr1 (pr2 (pr2 D))))
                  ( pr1 (pr1 D) , pr2 (pr2 (pr2 D))))
          ( inr b)
```
