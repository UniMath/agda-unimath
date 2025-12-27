### The derivative of the identity function is 1

```agda
module _
  {l : Level}
  ([a,b] : proper-closed-interval-ℝ l l)
  where

  abstract
    derivative-id-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( pr1)
        ( λ _ → raise-one-ℝ l)
    derivative-id-real-function-proper-closed-interval-ℝ =
      let
        open inequality-reasoning-Large-Poset ℝ-Large-Poset
      in
        is-derivative-modulus-of-real-function-proper-closed-interval-ℝ [a,b]
          ( _)
          ( _)
          ( λ ε →
            ( one-ℚ⁺ ,
              λ x y _ →
              chain-of-inequalities
                dist-ℝ (pr1 y -ℝ pr1 x) (raise-ℝ l one-ℝ *ℝ (pr1 y -ℝ pr1 x))
                ≤ dist-ℝ (pr1 y -ℝ pr1 x) (pr1 y -ℝ pr1 x)
                  by
                    leq-eq-ℝ
                      ( ap-dist-ℝ
                        ( refl)
                        ( ( eq-sim-ℝ
                            ( preserves-sim-right-mul-ℝ _ _ _
                              ( symmetric-sim-ℝ (sim-raise-ℝ _ _)))) ∙
                          ( left-unit-law-mul-ℝ _)))
                ≤ zero-ℝ
                  by leq-sim-ℝ (diagonal-dist-ℝ _)
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by
                    is-nonnegative-real-ℝ⁰⁺
                      ( nonnegative-real-ℚ⁺ ε *ℝ⁰⁺ nonnegative-dist-ℝ _ _)))
```
