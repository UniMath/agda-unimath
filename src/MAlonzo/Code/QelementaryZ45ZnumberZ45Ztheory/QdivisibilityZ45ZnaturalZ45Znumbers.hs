{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps

-- elementary-number-theory.divisibility-natural-numbers.div-ℕ
d_div'45'ℕ_4 :: Integer -> Integer -> ()
d_div'45'ℕ_4 = erased
-- elementary-number-theory.divisibility-natural-numbers.quotient-div-ℕ
d_quotient'45'div'45'ℕ_16 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  Integer
d_quotient'45'div'45'ℕ_16 ~v0 ~v1 v2
  = du_quotient'45'div'45'ℕ_16 v2
du_quotient'45'div'45'ℕ_16 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  Integer
du_quotient'45'div'45'ℕ_16 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.d_pr1_26
      (coe v0)
-- elementary-number-theory.divisibility-natural-numbers.eq-quotient-div-ℕ
d_eq'45'quotient'45'div'45'ℕ_30 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'quotient'45'div'45'ℕ_30 = erased
-- elementary-number-theory.divisibility-natural-numbers.eq-quotient-div-ℕ'
d_eq'45'quotient'45'div'45'ℕ''_44 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'quotient'45'div'45'ℕ''_44 = erased
-- elementary-number-theory.divisibility-natural-numbers.concatenate-eq-div-ℕ
d_concatenate'45'eq'45'div'45'ℕ_58 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'eq'45'div'45'ℕ_58 ~v0 ~v1 ~v2 ~v3 v4
  = du_concatenate'45'eq'45'div'45'ℕ_58 v4
du_concatenate'45'eq'45'div'45'ℕ_58 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'eq'45'div'45'ℕ_58 v0 = coe v0
-- elementary-number-theory.divisibility-natural-numbers.concatenate-div-eq-ℕ
d_concatenate'45'div'45'eq'45'ℕ_68 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'div'45'eq'45'ℕ_68 ~v0 ~v1 ~v2 v3 ~v4
  = du_concatenate'45'div'45'eq'45'ℕ_68 v3
du_concatenate'45'div'45'eq'45'ℕ_68 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'div'45'eq'45'ℕ_68 v0 = coe v0
-- elementary-number-theory.divisibility-natural-numbers.concatenate-eq-div-eq-ℕ
d_concatenate'45'eq'45'div'45'eq'45'ℕ_80 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_concatenate'45'eq'45'div'45'eq'45'ℕ_80 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du_concatenate'45'eq'45'div'45'eq'45'ℕ_80 v5
du_concatenate'45'eq'45'div'45'eq'45'ℕ_80 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_concatenate'45'eq'45'div'45'eq'45'ℕ_80 v0 = coe v0
-- elementary-number-theory.divisibility-natural-numbers.is-even-ℕ
d_is'45'even'45'ℕ_84 :: Integer -> ()
d_is'45'even'45'ℕ_84 = erased
-- elementary-number-theory.divisibility-natural-numbers.is-odd-ℕ
d_is'45'odd'45'ℕ_88 :: Integer -> ()
d_is'45'odd'45'ℕ_88 = erased
-- elementary-number-theory.divisibility-natural-numbers.div-one-ℕ
d_div'45'one'45'ℕ_94 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'one'45'ℕ_94 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe v0) erased
-- elementary-number-theory.divisibility-natural-numbers.div-is-one-ℕ
d_div'45'is'45'one'45'ℕ_104 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'is'45'one'45'ℕ_104 ~v0 v1 ~v2
  = du_div'45'is'45'one'45'ℕ_104 v1
du_div'45'is'45'one'45'ℕ_104 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'is'45'one'45'ℕ_104 v0 = coe d_div'45'one'45'ℕ_94 (coe v0)
-- elementary-number-theory.divisibility-natural-numbers.div-zero-ℕ
d_div'45'zero'45'ℕ_110 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'zero'45'ℕ_110 ~v0 = du_div'45'zero'45'ℕ_110
du_div'45'zero'45'ℕ_110 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'zero'45'ℕ_110
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (0 :: Integer)) erased
-- elementary-number-theory.divisibility-natural-numbers.div-is-zero-ℕ
d_div'45'is'45'zero'45'ℕ_120 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'is'45'zero'45'ℕ_120 ~v0 ~v1 ~v2
  = du_div'45'is'45'zero'45'ℕ_120
du_div'45'is'45'zero'45'ℕ_120 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'is'45'zero'45'ℕ_120 = coe du_div'45'zero'45'ℕ_110
-- elementary-number-theory.divisibility-natural-numbers.is-prop-div-ℕ
d_is'45'prop'45'div'45'ℕ_128 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'prop'45'div'45'ℕ_128 ~v0 ~v1 ~v2
  = du_is'45'prop'45'div'45'ℕ_128
du_is'45'prop'45'div'45'ℕ_128 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_is'45'prop'45'div'45'ℕ_128
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QpropositionalZ45Zmaps.du_is'45'prop'45'map'45'is'45'emb_46
-- elementary-number-theory.divisibility-natural-numbers.div-add-ℕ
d_div'45'add'45'ℕ_142 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'add'45'ℕ_142 ~v0 ~v1 ~v2 v3 v4
  = du_div'45'add'45'ℕ_142 v3 v4
du_div'45'add'45'ℕ_142 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'add'45'ℕ_142 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers.d_add'45'ℕ_4
                       (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-natural-numbers.div-left-summand-ℕ
d_div'45'left'45'summand'45'ℕ_178 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'left'45'summand'45'ℕ_178 v0
  = case coe v0 of
      0 -> coe
             (\ v1 v2 v3 ->
                seq
                  (coe v3)
                  (coe
                     (\ v4 ->
                        seq
                          (coe v4)
                          (coe
                             MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                             (coe (0 :: Integer)) erased))))
      _ -> coe
             (\ v1 v2 v3 v4 ->
                coe
                  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
                  (case coe v3 of
                     MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v5 v6
                       -> case coe v4 of
                            MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v7 v8
                              -> coe
                                   MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
                                   (coe v5) (coe v7)
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError)
                  erased)
-- elementary-number-theory.divisibility-natural-numbers.div-right-summand-ℕ
d_div'45'right'45'summand'45'ℕ_226 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'right'45'summand'45'ℕ_226 v0 v1 v2 v3 v4
  = coe d_div'45'left'45'summand'45'ℕ_178 v0 v2 v1 v3 v4
-- elementary-number-theory.divisibility-natural-numbers.is-zero-div-ℕ
d_is'45'zero'45'div'45'ℕ_242 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'div'45'ℕ_242 = erased
-- elementary-number-theory.divisibility-natural-numbers.refl-div-ℕ
d_refl'45'div'45'ℕ_262 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_refl'45'div'45'ℕ_262 ~v0 = du_refl'45'div'45'ℕ_262
du_refl'45'div'45'ℕ_262 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_refl'45'div'45'ℕ_262
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe (1 :: Integer)) erased
-- elementary-number-theory.divisibility-natural-numbers.antisymmetric-div-ℕ
d_antisymmetric'45'div'45'ℕ_272 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_antisymmetric'45'div'45'ℕ_272 = erased
-- elementary-number-theory.divisibility-natural-numbers.transitive-div-ℕ
d_transitive'45'div'45'ℕ_312 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_transitive'45'div'45'ℕ_312 ~v0 ~v1 ~v2 v3 v4
  = du_transitive'45'div'45'ℕ_312 v3 v4
du_transitive'45'div'45'ℕ_312 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_transitive'45'div'45'ℕ_312 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v2 v3
           -> case coe v1 of
                MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v4 v5
                  -> coe
                       MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
                       (coe v4) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-natural-numbers.div-mul-ℕ
d_div'45'mul'45'ℕ_348 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'mul'45'ℕ_348 v0 ~v1 ~v2 v3 = du_div'45'mul'45'ℕ_348 v0 v3
du_div'45'mul'45'ℕ_348 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'mul'45'ℕ_348 v0 v1
  = coe
      du_transitive'45'div'45'ℕ_312 (coe v1)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe v0) erased)
-- elementary-number-theory.divisibility-natural-numbers.preserves-div-mul-ℕ
d_preserves'45'div'45'mul'45'ℕ_364 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_preserves'45'div'45'mul'45'ℕ_364 ~v0 ~v1 ~v2 v3
  = du_preserves'45'div'45'mul'45'ℕ_364 v3
du_preserves'45'div'45'mul'45'ℕ_364 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_preserves'45'div'45'mul'45'ℕ_364 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-natural-numbers.reflects-div-mul-ℕ
d_reflects'45'div'45'mul'45'ℕ_392 ::
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_reflects'45'div'45'mul'45'ℕ_392 ~v0 ~v1 ~v2 ~v3 v4
  = du_reflects'45'div'45'mul'45'ℕ_392 v4
du_reflects'45'div'45'mul'45'ℕ_392 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_reflects'45'div'45'mul'45'ℕ_392 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (case coe v0 of
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30 v1 v2
           -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
      erased
-- elementary-number-theory.divisibility-natural-numbers.div-quotient-div-div-ℕ
d_div'45'quotient'45'div'45'div'45'ℕ_426 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'quotient'45'div'45'div'45'ℕ_426 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_div'45'quotient'45'div'45'div'45'ℕ_426 v5
du_div'45'quotient'45'div'45'div'45'ℕ_426 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'quotient'45'div'45'div'45'ℕ_426 v0
  = coe du_reflects'45'div'45'mul'45'ℕ_392 (coe v0)
-- elementary-number-theory.divisibility-natural-numbers.div-div-quotient-div-ℕ
d_div'45'div'45'quotient'45'div'45'ℕ_448 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'div'45'quotient'45'div'45'ℕ_448 ~v0 ~v1 ~v2 ~v3 v4
  = du_div'45'div'45'quotient'45'div'45'ℕ_448 v4
du_div'45'div'45'quotient'45'div'45'ℕ_448 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'div'45'quotient'45'div'45'ℕ_448 v0
  = coe du_preserves'45'div'45'mul'45'ℕ_364 (coe v0)
-- elementary-number-theory.divisibility-natural-numbers.is-zero-div-zero-ℕ
d_is'45'zero'45'div'45'zero'45'ℕ_462 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'div'45'zero'45'ℕ_462 = erased
-- elementary-number-theory.divisibility-natural-numbers.is-zero-is-zero-div-ℕ
d_is'45'zero'45'is'45'zero'45'div'45'ℕ_472 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'is'45'zero'45'div'45'ℕ_472 = erased
-- elementary-number-theory.divisibility-natural-numbers.is-one-div-one-ℕ
d_is'45'one'45'div'45'one'45'ℕ_480 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'div'45'one'45'ℕ_480 = erased
-- elementary-number-theory.divisibility-natural-numbers.is-one-div-ℕ
d_is'45'one'45'div'45'ℕ_490 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'div'45'ℕ_490 = erased
-- elementary-number-theory.divisibility-natural-numbers.div-eq-ℕ
d_div'45'eq'45'ℕ_504 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'eq'45'ℕ_504 ~v0 ~v1 ~v2 = du_div'45'eq'45'ℕ_504
du_div'45'eq'45'ℕ_504 ::
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'eq'45'ℕ_504 = coe du_refl'45'div'45'ℕ_262
-- elementary-number-theory.divisibility-natural-numbers.leq-div-succ-ℕ
d_leq'45'div'45'succ'45'ℕ_512 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_leq'45'div'45'succ'45'ℕ_512 = erased
-- elementary-number-theory.divisibility-natural-numbers.leq-div-ℕ
d_leq'45'div'45'ℕ_526 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  AgdaAny
d_leq'45'div'45'ℕ_526 = erased
-- elementary-number-theory.divisibility-natural-numbers.is-one-is-divisor-below-ℕ
d_is'45'one'45'is'45'divisor'45'below'45'ℕ_550 ::
  Integer -> Integer -> ()
d_is'45'one'45'is'45'divisor'45'below'45'ℕ_550 = erased
-- elementary-number-theory.divisibility-natural-numbers.is-nonzero-quotient-div-ℕ
d_is'45'nonzero'45'quotient'45'div'45'ℕ_564 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4
d_is'45'nonzero'45'quotient'45'div'45'ℕ_564 = erased
