### The derivative of a constant function is 0

```agda
module _
  {l1 l2 : Level}
  ([a,b] : proper-closed-interval-ℝ l1 l1)
  (c : ℝ l2)
  where

  abstract
    derivative-constant-real-function-proper-closed-interval-ℝ :
      is-derivative-real-function-proper-closed-interval-ℝ
        ( [a,b])
        ( λ _ → c)
        ( λ _ → raise-ℝ (l1 ⊔ l2) zero-ℝ)
    derivative-constant-real-function-proper-closed-interval-ℝ =
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
                dist-ℝ (c -ℝ c) (raise-ℝ (l1 ⊔ l2) zero-ℝ *ℝ (pr1 y -ℝ pr1 x))
                ≤ dist-ℝ zero-ℝ zero-ℝ
                  by
                    leq-sim-ℝ
                      ( preserves-dist-sim-ℝ
                        ( right-inverse-law-add-ℝ c)
                        ( similarity-reasoning-ℝ
                            raise-ℝ (l1 ⊔ l2) zero-ℝ *ℝ (pr1 y -ℝ pr1 x)
                            ~ℝ zero-ℝ *ℝ (pr1 y -ℝ pr1 x)
                              by
                                preserves-sim-right-mul-ℝ _ _ _
                                  ( symmetric-sim-ℝ (sim-raise-ℝ _ zero-ℝ))
                            ~ℝ zero-ℝ
                              by left-zero-law-mul-ℝ _))
                ≤ zero-ℝ
                  by leq-sim-ℝ (diagonal-dist-ℝ zero-ℝ)
                ≤ real-ℚ⁺ ε *ℝ dist-ℝ (pr1 x) (pr1 y)
                  by
                    is-nonnegative-real-ℝ⁰⁺
                      ( nonnegative-real-ℚ⁺ ε *ℝ⁰⁺ nonnegative-dist-ℝ _ _)))
```
